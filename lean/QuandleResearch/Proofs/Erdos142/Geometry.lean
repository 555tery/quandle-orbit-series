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

lemma no_int_neg_one_zero (j : ℤ) (hl : -(1 : ℝ) < (j : ℝ))
    (hr : (j : ℝ) < 0) : False := by
  have hl' : (-1 : ℤ) < j := by exact_mod_cast hl
  have hr' : j < 0 := by exact_mod_cast hr
  omega

lemma no_int_neg_two_neg_one (j : ℤ) (hl : -(2 : ℝ) < (j : ℝ))
    (hr : (j : ℝ) < -1) : False := by
  have hl' : (-2 : ℤ) < j := by exact_mod_cast hl
  have hr' : j < -1 := by exact_mod_cast hr
  omega

lemma no_int_zero_one (j : ℤ) (hl : (0 : ℝ) < (j : ℝ))
    (hr : (j : ℝ) < 1) : False := by
  have hl' : 0 < j := by exact_mod_cast hl
  have hr' : j < 1 := by exact_mod_cast hr
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
  · exact no_int_neg_one_zero j (by linarith) (by linarith)
  · exact no_int_neg_two_neg_one j (by linarith) (by linarith)

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
  · exact no_int_neg_one_zero j (by linarith) (by linarith)
  · exact no_int_zero_one j (by linarith) (by linarith)
  · exact no_int_neg_two_neg_one j (by linarith) (by linarith)
  · exact no_int_neg_one_zero j (by linarith) (by linarith)

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
  · exact no_up_LH (j := j) hz hx hy hc (Or.inl rfl) (by linarith) (by linarith)
  · exact no_up_HH hx hz hy hs
  · exact no_up_HH hx hz hy hs
  · exact no_up_LH (j := j) hz hx hy hc (Or.inr rfl) (by linarith) (by linarith)
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
    ring
  · refine ⟨a - 3 / 4, Or.inr ⟨h, 1, by omega, by omega, ?_⟩⟩
    ring

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



/-! A rational inner rectangle certificate.  The 480 vertical strips use
horizontal radii with denominator 2400.  We first establish containment
and an exact sum of rectangle areas, separately from measure additivity. -/

def lowerRadiusUnits (i : ℕ) : ℕ := min 600 (120 + 3 * i)

def upperRadiusUnits (j : ℕ) : ℕ :=
  min 300 (min (240 + 3 * j) (480 - 3 * (j + 1)))

lemma lower_rectangle_mem {i : ℕ} {s a : ℝ} (hi : i < 240)
    (hs₁ : (i : ℝ) / 480 < s)
    (hs₂ : s < ((i : ℝ) + 1) / 480)
    (ha : |a| < (lowerRadiusUnits i : ℝ) / 2400) :
    Lower s a := by
  have hi' : (i : ℝ) < 240 := by exact_mod_cast hi
  have hi0 : 0 ≤ (i : ℝ) := by positivity
  have hi1 : (i : ℝ) + 1 ≤ 240 := by
    exact_mod_cast (show i + 1 ≤ 240 by omega)
  have hcap : (lowerRadiusUnits i : ℝ) ≤ 600 := by
    exact_mod_cast (min_le_left 600 (120 + 3 * i))
  have hlin : (lowerRadiusUnits i : ℝ) ≤ 120 + 3 * (i : ℝ) := by
    exact_mod_cast (min_le_right 600 (120 + 3 * i))
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma upper_rectangle_mem {j : ℕ} {s u : ℝ} (hj₁ : 2 ≤ j)
    (hj₂ : j < 160)
    (hs₁ : (240 + (j : ℝ)) / 480 < s)
    (hs₂ : s < (240 + (j : ℝ) + 1) / 480)
    (hu : |u| < (upperRadiusUnits j : ℝ) / 2400) :
    Upper s u := by
  have hj₁' : 2 ≤ (j : ℝ) := by exact_mod_cast hj₁
  have hj₂' : (j : ℝ) + 1 ≤ 160 := by
    exact_mod_cast (show j + 1 ≤ 160 by omega)
  have hcap : (upperRadiusUnits j : ℝ) ≤ 300 := by
    exact_mod_cast (min_le_left 300 (min (240 + 3 * j) (480 - 3 * (j + 1))))
  have hleft : (upperRadiusUnits j : ℝ) ≤ 240 + 3 * (j : ℝ) := by
    exact_mod_cast (show upperRadiusUnits j ≤ 240 + 3 * j from
      le_trans (min_le_right _ _) (min_le_left _ _))
  have hrightN : upperRadiusUnits j ≤ 480 - 3 * (j + 1) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hrightN' : upperRadiusUnits j + 3 * (j + 1) ≤ 480 := by omega
  have hright : (upperRadiusUnits j : ℝ) + 3 * ((j : ℝ) + 1) ≤ 480 := by
    exact_mod_cast hrightN'
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Distinct strips have disjoint open vertical intervals. -/
lemma strips_disjoint {i j : ℕ} {s : ℝ} (hij : i ≠ j)
    (hi₁ : (i : ℝ) / 480 < s)
    (hi₂ : s < ((i : ℝ) + 1) / 480)
    (hj₁ : (j : ℝ) / 480 < s)
    (hj₂ : s < ((j : ℝ) + 1) / 480) : False := by
  rcases lt_or_gt_of_ne hij with h | h
  · have h' : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (show i + 1 ≤ j by omega)
    linarith
  · have h' : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast (show j + 1 ≤ i by omega)
    linarith

/-- Lower rectangles count their full horizontal widths in units 1/2400;
upper rectangles count both arcs.  Multiplying by the height 1/480
gives the rational inner area certificate. -/
def lowerAreaUnits : ℕ :=
  ∑ i ∈ Finset.range 240, 2 * lowerRadiusUnits i

def upperAreaUnits : ℕ :=
  ∑ j ∈ Finset.range 158, 4 * upperRadiusUnits (j + 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rectangle_area_units :
    lowerAreaUnits = 210720 ∧ upperAreaUnits = 126948 := by
  decide

/-- Strict numerical comparison for the inner rectangles, not yet a
measure/cardinality theorem about the torus. -/
theorem rectangle_area_comparison :
    (7 / 24 : ℚ) <
      ((lowerAreaUnits + upperAreaUnits : ℕ) : ℚ) / (480 * 2400) := by
  rw [rectangle_area_units.1, rectangle_area_units.2]
  norm_num



/-! Finite-grid preparation: use interior lattice points in rational cells.
These lemmas do not assume that the modulus is divisible by the grid
denominator, so they will also apply to large prime moduli. -/

def gridLift (x : ℝ) (t : ℕ) : ℤ := ⌊x⌋ + (t : ℤ) + 1

lemma gridLift_bounds (x : ℝ) (t : ℕ) :
    x < (gridLift x t : ℝ) ∧
      (gridLift x t : ℝ) ≤ x + (t : ℝ) + 1 := by
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  have ht : 0 ≤ (t : ℝ) := by positivity
  unfold gridLift
  push_cast
  constructor <;> linarith

def cellLift (i : ℤ) (w : ℝ) (t : ℕ) : ℤ :=
  gridLift ((i : ℝ) * w) t

lemma cellLift_mem {i : ℤ} {w : ℝ} {t : ℕ}
    (ht : (t : ℝ) + 1 < w) :
    (i : ℝ) * w < (cellLift i w t : ℝ) ∧
      (cellLift i w t : ℝ) < ((i : ℝ) + 1) * w := by
  have h := gridLift_bounds ((i : ℝ) * w) t
  unfold cellLift
  constructor
  · exact h.1
  · nlinarith [h.2]

lemma cellLift_injective {i j : ℤ} {w : ℝ} {t u : ℕ}
    (hw : 0 < w) (ht : (t : ℝ) + 1 < w)
    (hu : (u : ℝ) + 1 < w)
    (he : cellLift i w t = cellLift j w u) :
    i = j ∧ t = u := by
  have hi := cellLift_mem (i := i) ht
  have hj := cellLift_mem (i := j) hu
  have hc : (cellLift i w t : ℝ) = (cellLift j w u : ℝ) := by rw [he]
  have hij : i = j := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hh : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast (show i + 1 ≤ j by omega)
      have hm := mul_le_mul_of_nonneg_right hh hw.le
      linarith [hi.2, hj.1]
    · have hh : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast (show j + 1 ≤ i by omega)
      have hm := mul_le_mul_of_nonneg_right hh hw.le
      linarith [hj.2, hi.1]
  subst j
  unfold cellLift gridLift at he
  exact ⟨rfl, by omega⟩

/-- Each cell of a grid of denominator d contains q interior lattice
points at modulus p, whenever q*d < p.  The actual normalized lattice
points lie in the open cell, not merely its closure. -/
lemma normalized_cellLift_mem {i : ℤ} {p d : ℝ} {t : ℕ}
    (hp : 0 < p) (hd : 0 < d) (ht : ((t : ℝ) + 1) * d < p) :
    (i : ℝ) / d < (cellLift i (p / d) t : ℝ) / p ∧
      (cellLift i (p / d) t : ℝ) / p < ((i : ℝ) + 1) / d := by
  have h := cellLift_mem (i := i) ((lt_div_iff₀ hd).2 ht)
  constructor
  · apply (lt_div_iff₀ hp).2
    calc
      (i : ℝ) / d * p = (i : ℝ) * (p / d) := by ring
      _ < (cellLift i (p / d) t : ℝ) := h.1
  · apply (div_lt_iff₀ hp).2
    calc
      (cellLift i (p / d) t : ℝ) < ((i : ℝ) + 1) * (p / d) := h.2
      _ = ((i : ℝ) + 1) / d * p := by ring

/-! Tensorization of the pointwise quantitative Jensen bound. -/

/-- Coordinatewise modular APs in any finite product obey the summed
potential gap. No measure or probabilistic assumption is used here. -/
theorem product_potential_gap {ι : Type*} [Fintype ι]
    (sx sy sz ax ay az ux uy uz : ι → ℝ) (j k : ι → ℤ)
    (hx : ∀ i, HasLocal (sx i) (ax i) (ux i))
    (hy : ∀ i, HasLocal (sy i) (ay i) (uy i))
    (hz : ∀ i, HasLocal (sz i) (az i) (uz i))
    (hs : ∀ i, 2 * sy i = sx i + sz i + (k i : ℝ))
    (ha : ∀ i, ax i + az i - 2 * ay i = (j i : ℝ)) :
    (∑ i, ((sx i - sz i)^2 + (ax i - az i)^2)) ≤
      (∑ i, potential (sx i) (ux i)) +
      (∑ i, potential (sz i) (uz i)) -
      2 * (∑ i, potential (sy i) (uy i)) := by
  calc
    _ ≤ ∑ i, (potential (sx i) (ux i) + potential (sz i) (uz i) -
          2 * potential (sy i) (uy i)) :=
      Finset.sum_le_sum fun i _ => potential_gap (hx i) (hy i) (hz i) (hs i) (ha i)
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- If all three points have total potentials in the same interval of
width w, then their squared endpoint separation is at most 2*w. -/
theorem shell_endpoint_bound {ι : Type*} [Fintype ι]
    (sx sy sz ax ay az ux uy uz : ι → ℝ) (j k : ι → ℤ)
    (hx : ∀ i, HasLocal (sx i) (ax i) (ux i))
    (hy : ∀ i, HasLocal (sy i) (ay i) (uy i))
    (hz : ∀ i, HasLocal (sz i) (az i) (uz i))
    (hs : ∀ i, 2 * sy i = sx i + sz i + (k i : ℝ))
    (ha : ∀ i, ax i + az i - 2 * ay i = (j i : ℝ))
    (b w : ℝ)
    (hxs : (∑ i, potential (sx i) (ux i)) ≤ b + w)
    (hys : b ≤ ∑ i, potential (sy i) (uy i))
    (hzs : (∑ i, potential (sz i) (uz i)) ≤ b + w) :
    (∑ i, ((sx i - sz i)^2 + (ax i - az i)^2)) ≤ 2 * w := by
  have h := product_potential_gap sx sy sz ax ay az ux uy uz j k hx hy hz hs ha
  linarith



/-! An exact finite indexing type for the rational inner cells.  The lower
column index is signed; upper columns use the two centers 600 and 1800
in units of 1/2400. -/

def innerCellCoords :
    ((Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2)))) →
      ℤ × ℤ
  | Sum.inl ⟨i, k⟩ => ((i.val : ℤ),
      (k.val : ℤ) - (lowerRadiusUnits i.val : ℤ))
  | Sum.inr ⟨j, l, k⟩ => ((j.val : ℤ) + 242,
      600 + 1200 * (l.val : ℤ) + (k.val : ℤ) -
        (upperRadiusUnits (j.val + 2) : ℤ))

theorem inner_cell_index_card :
    Fintype.card ((Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2)))) =
      lowerAreaUnits + upperAreaUnits := by
  classical
  simp [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    Finset.sum_range, lowerAreaUnits, upperAreaUnits, ← Nat.mul_assoc]

lemma horizontal_cell_radius {R k : ℕ} (hk : k < 2 * R)
    {a c : ℝ}
    (h₁ : (c + (k : ℝ) - (R : ℝ)) / 2400 < a)
    (h₂ : a < (c + (k : ℝ) - (R : ℝ) + 1) / 2400) :
    |a - c / 2400| < (R : ℝ) / 2400 := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hk1 : (k : ℝ) + 1 ≤ 2 * (R : ℝ) := by
    exact_mod_cast (show k + 1 ≤ 2 * R by omega)
  apply abs_lt.mpr
  constructor <;> linarith

/-- Every point in an indexed open cell belongs to the geometric block. -/
theorem inner_cell_mem
    (e : (Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2))))
    {s a : ℝ}
    (hs₁ : ((innerCellCoords e).1 : ℝ) / 480 < s)
    (hs₂ : s < (((innerCellCoords e).1 : ℝ) + 1) / 480)
    (ha₁ : ((innerCellCoords e).2 : ℝ) / 2400 < a)
    (ha₂ : a < (((innerCellCoords e).2 : ℝ) + 1) / 2400) :
    InBlock s a := by
  rcases e with ⟨i, k⟩ | ⟨j, l, k⟩
  · simp only [innerCellCoords, Int.cast_natCast, Int.cast_sub] at hs₁ hs₂ ha₁ ha₂
    have hr := horizontal_cell_radius k.isLt (c := 0) (a := a)
      (by linarith [ha₁]) (by linarith [ha₂])
    apply Or.inl
    exact lower_rectangle_mem i.isLt hs₁ hs₂ (by simpa using hr)
  · simp only [innerCellCoords, Int.cast_natCast, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_ofNat] at hs₁ hs₂ ha₁ ha₂
    have hr := horizontal_cell_radius k.isLt (c := 600 + 1200 * (l.val : ℝ))
      (a := a) (by linarith [ha₁]) (by linarith [ha₂])
    have hj₁ : 2 ≤ j.val + 2 := by omega
    have hj₂ : j.val + 2 < 160 := by have := j.isLt; omega
    have hsl : (240 + ((j.val + 2 : ℕ) : ℝ)) / 480 < s := by
      push_cast
      linarith
    have hsu : s < (240 + ((j.val + 2 : ℕ) : ℝ) + 1) / 480 := by
      push_cast
      linarith
    have hl : l.val = 0 ∨ l.val = 1 := by have := l.isLt; omega
    rcases hl with hl | hl
    · right; left
      rw [hl] at hr
      norm_num at hr
      exact upper_rectangle_mem hj₁ hj₂ hsl hsu hr
    · right; right
      rw [hl] at hr
      norm_num at hr
      exact upper_rectangle_mem hj₁ hj₂ hsl hsu hr

/-- On an interval of width strictly less than p, integer representatives
of a residue in ZMod p are unique.  This uses Mathlib's native ZMod. -/
lemma intCast_injective_close {p : ℕ} {a b : ℤ}
    (h₁ : a - b < (p : ℤ)) (h₂ : b - a < (p : ℤ))
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hd : (p : ℤ) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp h
  by_cases hn : 0 ≤ b - a
  · have he := Int.eq_zero_of_dvd_of_nonneg_of_lt hn h₂ hd
    omega
  · have hd' : (p : ℤ) ∣ a - b := by
      have he : a - b = -(b - a) := by ring
      rw [he]
      exact dvd_neg.mpr hd
    have he := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (show 0 ≤ a - b by omega) h₁ hd'
    omega

/-- A modular progression of integer lifts gives the real-lift equation
required by the geometric lemmas, after normalization by p. -/
lemma normalized_modular_AP {p : ℕ} (hp : 0 < p) {x y z : ℤ}
    (h : (x : ZMod p) + (z : ZMod p) = 2 * (y : ZMod p)) :
    ∃ j : ℤ, (x : ℝ) / (p : ℝ) + (z : ℝ) / (p : ℝ) -
      2 * ((y : ℝ) / (p : ℝ)) = (j : ℝ) := by
  have hzero : ((x + z - 2 * y : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [h]
    ring
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hj' : (x : ℝ) + (z : ℝ) - 2 * (y : ℝ) = (p : ℝ) * (j : ℝ) := by
    exact_mod_cast hj
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  refine ⟨j, ?_⟩
  field_simp [hp']
  linarith



/-! Inject the product of the inner-cell index with two finite offset
ranges into the actual finite torus, including wraparound of signed
horizontal coordinates. -/

lemma innerCellCoords_injective : Function.Injective innerCellCoords := by
  intro e f h
  rcases e with ⟨i, k⟩ | ⟨j, l, k⟩ <;>
    rcases f with ⟨i', k'⟩ | ⟨j', l', k'⟩
  · have hr := congrArg Prod.fst h
    change (i.val : ℤ) = (i'.val : ℤ) at hr
    have hi : i = i' := Fin.ext (by omega)
    subst i'
    have hc := congrArg Prod.snd h
    change (k.val : ℤ) - (lowerRadiusUnits i.val : ℤ) =
      (k'.val : ℤ) - (lowerRadiusUnits i.val : ℤ) at hc
    have hk : k = k' := Fin.ext (by omega)
    subst k'
    rfl
  · have hr := congrArg Prod.fst h
    change (i.val : ℤ) = (j'.val : ℤ) + 242 at hr
    have hi := i.isLt
    omega
  · have hr := congrArg Prod.fst h
    change (j.val : ℤ) + 242 = (i'.val : ℤ) at hr
    have hi := i'.isLt
    omega
  · have hr := congrArg Prod.fst h
    change (j.val : ℤ) + 242 = (j'.val : ℤ) + 242 at hr
    have hj : j = j' := Fin.ext (by omega)
    subst j'
    have hc := congrArg Prod.snd h
    change 600 + 1200 * (l.val : ℤ) + (k.val : ℤ) -
      (upperRadiusUnits (j.val + 2) : ℤ) =
      600 + 1200 * (l'.val : ℤ) + (k'.val : ℤ) -
      (upperRadiusUnits (j.val + 2) : ℤ) at hc
    have hR : upperRadiusUnits (j.val + 2) ≤ 300 := min_le_left _ _
    have hk := k.isLt
    have hk' := k'.isLt
    have hl : l = l' := Fin.ext (by omega)
    subst l'
    have he : k = k' := Fin.ext (by omega)
    subst k'
    rfl

/-- The horizontal lifts are unique modulo one for a fixed vertical
coordinate.  The union of all bands need not fit in one length-one
interval, so the equal-row hypothesis is essential. -/
lemma block_horizontal_close {s a b : ℝ}
    (ha : InBlock s a) (hb : InBlock s b) :
    a - b < 1 ∧ b - a < 1 := by
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · have h₁ := abs_lt.mp ha.2.2.1
    have h₂ := abs_lt.mp hb.2.2.1
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · linarith [ha.2.1, hb.1]
  · linarith [ha.2.1, hb.1]
  · linarith [ha.1, hb.2.1]
  · have h₁ := abs_lt.mp ha.2.2.1
    have h₂ := abs_lt.mp hb.2.2.1
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · have h₁ := abs_lt.mp ha.2.2.1
    have h₂ := abs_lt.mp hb.2.2.1
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · linarith [ha.1, hb.2.1]
  · have h₁ := abs_lt.mp ha.2.2.1
    have h₂ := abs_lt.mp hb.2.2.1
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · have h₁ := abs_lt.mp ha.2.2.1
    have h₂ := abs_lt.mp hb.2.2.1
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma int_close_of_normalized_close {p : ℕ} (hp : 0 < p) {a b : ℤ}
    (h₁ : (a : ℝ) / (p : ℝ) - (b : ℝ) / (p : ℝ) < 1)
    (h₂ : (b : ℝ) / (p : ℝ) - (a : ℝ) / (p : ℝ) < 1) :
    a - b < (p : ℤ) ∧ b - a < (p : ℤ) := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  rw [← sub_div] at h₁ h₂
  have h₁' := (div_lt_iff₀ hp').mp h₁
  have h₂' := (div_lt_iff₀ hp').mp h₂
  rw [one_mul] at h₁' h₂'
  exact ⟨by exact_mod_cast h₁', by exact_mod_cast h₂'⟩

def innerPointLifts (p : ℕ)
    (e : (Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2))))
    (t u : ℕ) : ℤ × ℤ :=
  (cellLift (innerCellCoords e).1 ((p : ℝ) / 480) t,
    cellLift (innerCellCoords e).2 ((p : ℝ) / 2400) u)

lemma innerPoint_mem (p : ℕ) (hp : 0 < p)
    (e : (Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2))))
    (t u : ℕ) (ht : (t + 1) * 480 < p) (hu : (u + 1) * 2400 < p) :
    InBlock ((innerPointLifts p e t u).1 / (p : ℝ))
      ((innerPointLifts p e t u).2 / (p : ℝ)) := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have ht' : ((t : ℝ) + 1) * 480 < (p : ℝ) := by exact_mod_cast ht
  have hu' : ((u : ℝ) + 1) * 2400 < (p : ℝ) := by exact_mod_cast hu
  have h₁ := normalized_cellLift_mem (i := (innerCellCoords e).1)
    hp' (show (0 : ℝ) < 480 by norm_num) ht'
  have h₂ := normalized_cellLift_mem (i := (innerCellCoords e).2)
    hp' (show (0 : ℝ) < 2400 by norm_num) hu'
  exact inner_cell_mem e h₁.1 h₁.2 h₂.1 h₂.2

/-- The finite block is defined by existence of genuine lifts in InBlock,
rather than by a separately postulated density. -/
def finiteBlock (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter fun v => ∃ x y : ℤ,
    (x : ZMod p) = v.1 ∧ (y : ZMod p) = v.2 ∧
      InBlock ((x : ℝ) / (p : ℝ)) ((y : ℝ) / (p : ℝ))

lemma offset_mul_lt {t q p d : ℕ} (ht : t < q) (hq : q * d < p) :
    (t + 1) * d < p :=
  lt_of_le_of_lt (Nat.mul_le_mul_right d (Nat.succ_le_of_lt ht)) hq

set_option maxRecDepth 8192 in
theorem finite_block_card_lower (p q r : ℕ) [NeZero p]
    (hq : q * 480 < p) (hr : r * 2400 < p) :
    (lowerAreaUnits + upperAreaUnits) * q * r ≤ (finiteBlock p).card := by
  classical
  have hp : 0 < p := by omega
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  let E := (Σ i : Fin 240, Fin (2 * lowerRadiusUnits i.val)) ⊕
      (Σ j : Fin 158, Fin 2 × Fin (2 * upperRadiusUnits (j.val + 2)))
  let g : E × Fin q × Fin r → ZMod p × ZMod p := fun e =>
    ((innerPointLifts p e.1 e.2.1.val e.2.2.val).1,
      (innerPointLifts p e.1 e.2.1.val e.2.2.val).2)
  have hm (e : E × Fin q × Fin r) :
      InBlock ((innerPointLifts p e.1 e.2.1.val e.2.2.val).1 / (p : ℝ))
        ((innerPointLifts p e.1 e.2.1.val e.2.2.val).2 / (p : ℝ)) := by
    apply innerPoint_mem p hp
    · exact offset_mul_lt e.2.1.isLt hq
    · exact offset_mul_lt e.2.2.isLt hr
  have hg (e : E × Fin q × Fin r) : g e ∈ finiteBlock p := by
    unfold finiteBlock
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, _, _, rfl, rfl, hm e⟩
  have hinj : Function.Injective g := by
    rintro ⟨e, t, u⟩ ⟨f, t', u'⟩ he
    let x := innerPointLifts p e t.val u.val
    let y := innerPointLifts p f t'.val u'.val
    have hx : InBlock ((x.1 : ℝ) / p) ((x.2 : ℝ) / p) := hm (e, t, u)
    have hy : InBlock ((y.1 : ℝ) / p) ((y.2 : ℝ) / p) := hm (f, t', u')
    have hsx := block_s_bounds hx
    have hsy := block_s_bounds hy
    have hs := int_close_of_normalized_close hp (a := x.1) (b := y.1)
      (by linarith [hsx.2, hsy.1]) (by linarith [hsy.2, hsx.1])
    have hxs : x.1 = y.1 := intCast_injective_close hs.1 hs.2 (congrArg Prod.fst he)
    have hy' : InBlock ((x.1 : ℝ) / p) ((y.2 : ℝ) / p) := by
      rw [hxs]
      exact hy
    have ha := block_horizontal_close hx hy'
    have ha' := int_close_of_normalized_close hp ha.1 ha.2
    have hxa : x.2 = y.2 := intCast_injective_close ha'.1 ha'.2 (congrArg Prod.snd he)
    have ht : (t.val : ℝ) + 1 < (p : ℝ) / 480 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 480)).2
      exact_mod_cast (show (t.val + 1) * 480 < p from offset_mul_lt t.isLt hq)
    have ht' : (t'.val : ℝ) + 1 < (p : ℝ) / 480 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 480)).2
      exact_mod_cast (show (t'.val + 1) * 480 < p from offset_mul_lt t'.isLt hq)
    have hu : (u.val : ℝ) + 1 < (p : ℝ) / 2400 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2400)).2
      exact_mod_cast (show (u.val + 1) * 2400 < p from offset_mul_lt u.isLt hr)
    have hu' : (u'.val : ℝ) + 1 < (p : ℝ) / 2400 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2400)).2
      exact_mod_cast (show (u'.val + 1) * 2400 < p from offset_mul_lt u'.isLt hr)
    have hrow := cellLift_injective (by positivity : 0 < (p : ℝ) / 480) ht ht' hxs
    have hcol := cellLift_injective (by positivity : 0 < (p : ℝ) / 2400) hu hu' hxa
    have hef : e = f := innerCellCoords_injective (Prod.ext hrow.1 hcol.1)
    have htt : t = t' := Fin.ext hrow.2
    have huu : u = u' := Fin.ext hcol.2
    subst f
    subst t'
    subst u'
    rfl
  let emb : E × Fin q × Fin r → ↥(finiteBlock p) := fun e => ⟨g e, hg e⟩
  have hc := Fintype.card_le_of_injective emb
    (show Function.Injective emb from fun _ _ he => hinj (congrArg Subtype.val he))
  have hE : Fintype.card E = lowerAreaUnits + upperAreaUnits := inner_cell_index_card
  simpa only [Fintype.card_prod, Fintype.card_fin, hE, Fintype.card_coe, Nat.mul_assoc] using hc



/-! A uniform positive density margin for sufficiently large moduli. -/

set_option maxRecDepth 8192 in
theorem finite_block_density (p : ℕ) [NeZero p] (hp : 2400000 ≤ p) :
    73 * p ^ 2 ≤ 250 * (finiteBlock p).card := by
  let q := (p - 1) / 480
  let r := (p - 1) / 2400
  have hq : q * 480 < p := by dsimp [q]; omega
  have hr : r * 2400 < p := by dsimp [r]; omega
  have hqlo : 999 * p ≤ 480000 * q := by dsimp [q]; omega
  have hrlo : 999 * p ≤ 2400000 * r := by dsimp [r]; omega
  have hcard := finite_block_card_lower p q r hq hr
  rw [rectangle_area_units.1, rectangle_area_units.2] at hcard
  have hq' : 999 * (p : ℝ) ≤ 480000 * (q : ℝ) := by exact_mod_cast hqlo
  have hr' : 999 * (p : ℝ) ≤ 2400000 * (r : ℝ) := by exact_mod_cast hrlo
  have hc : 337668 * (q : ℝ) * (r : ℝ) ≤ ((finiteBlock p).card : ℝ) := by
    exact_mod_cast hcard
  have hprod := mul_le_mul hq' hr' (by positivity) (by positivity)
  have hgoal : 73 * (p : ℝ)^2 ≤ 250 * ((finiteBlock p).card : ℝ) := by
    nlinarith [sq_nonneg (p : ℝ)]
  exact_mod_cast hgoal

/-! Finite averaging without measure theory.  We avoid all short
endpoint differences by the choice of slope before choosing a shift.
No independence or estimate of the number of progressions is assumed. -/

/-- If the union of forbidden sets has cardinality below the size
of the ambient group, one choice avoids every forbidden set. -/
theorem exists_avoid_bad {ι G : Type*} [Fintype G] [DecidableEq G]
    (I : Finset ι) (bad : ι → Finset G) (M : ℕ)
    (hb : ∀ i ∈ I, (bad i).card ≤ M)
    (h : I.card * M < Fintype.card G) :
    ∃ a : G, ∀ i ∈ I, a ∉ bad i := by
  classical
  have hcard := Finset.card_biUnion_le_card_mul I bad M hb
  have hn : ¬ ∀ a : G, a ∈ I.biUnion bad := by
    intro hall
    have hsub : (Finset.univ : Finset G) ⊆ I.biUnion bad := fun a _ => hall a
    have hh := Finset.card_le_card hsub
    rw [Finset.card_univ] at hh
    omega
  obtain ⟨a, ha⟩ := not_forall.mp hn
  exact ⟨a, fun i hi hm => ha (Finset.mem_biUnion.mpr ⟨i, hi, hm⟩)⟩

/-- Choose a slope avoiding the forbidden set D for every positive
difference of indices below N, provided multiplication by each such
difference is a bijection of the ambient finite additive group. -/
theorem exists_avoiding_slope {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (N : ℕ) (D : Finset G)
    (e : ℕ → G ≃ G)
    (he : ∀ d ∈ Finset.Ico 1 N, ∀ a : G, e d a = d • a)
    (h : N * D.card < Fintype.card G) :
    ∃ a : G, ∀ d ∈ Finset.Ico 1 N, d • a ∉ D := by
  classical
  let I := Finset.Ico 1 N
  let bad : ℕ → Finset G := fun d => D.map (e d).symm.toEmbedding
  have hI : I.card ≤ N := by
    have hh : I ⊆ Finset.range N := by
      intro d hd
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2
    simpa using Finset.card_le_card hh
  have hb : ∀ d ∈ I, (bad d).card ≤ D.card := by
    intro d _
    simp [bad]
  obtain ⟨a, ha⟩ := exists_avoid_bad I bad D.card hb
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hI) h)
  refine ⟨a, ?_⟩
  intro d hd hm
  apply ha d hd
  apply Finset.mem_map.mpr
  refine ⟨e d a, ?_, ?_⟩
  · rwa [he d hd a]
  · simp

/-- Averaging over all shifts: a fiber of the map (i,y) ↦ y-f(i)
supplies the large preimage. -/
theorem shift_large_preimage {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (I : Finset ℕ) (S : Finset G) (f : ℕ → G) (K : ℕ)
    (h : Fintype.card G * K ≤ I.card * S.card) :
    ∃ b : G, K ≤ (I.filter fun i => f i + b ∈ S).card := by
  classical
  let g : ℕ × G → G := fun v => v.2 - f v.1
  have h' : (Finset.univ : Finset G).card * K ≤ (I.product S).card := by
    simpa using h
  obtain ⟨b, _, hb⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := g) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty h'
  let T := (I.product S).filter fun v => g v = b
  let P := I.filter fun i => f i + b ∈ S
  have hm : Set.MapsTo (Prod.fst : ℕ × G → ℕ) T P := by
    intro v hv
    have hmem := Finset.mem_filter.mp (show v ∈ T from hv)
    have hv' := Finset.mem_product.mp hmem.1
    have heq : f v.1 + b = v.2 := by
      have hg : v.2 - f v.1 = b := hmem.2
      calc
        f v.1 + b = f v.1 + (v.2 - f v.1) := by rw [hg]
        _ = v.2 := by abel
    change v.1 ∈ I.filter (fun i => f i + b ∈ S)
    exact Finset.mem_filter.mpr ⟨hv'.1, by simpa only [heq] using hv'.2⟩
  have hi : (T : Set (ℕ × G)).InjOn (Prod.fst : ℕ × G → ℕ) := by
    intro v hv w hw he
    have h₁ := (Finset.mem_filter.mp (show v ∈ T from hv)).2
    have h₂ := (Finset.mem_filter.mp (show w ∈ T from hw)).2
    change v.2 - f v.1 = b at h₁
    change w.2 - f w.1 = b at h₂
    rw [he] at h₁
    exact Prod.ext he (by
      calc
        v.2 = (v.2 - f w.1) + f w.1 := by abel
        _ = (w.2 - f w.1) + f w.1 := by rw [h₁, h₂]
        _ = w.2 := by abel)
  exact ⟨b, le_trans hb (Finset.card_le_card_of_injOn Prod.fst hm hi)⟩

/-- Deterministic transfer to Mathlib's actual extremal function.
The only shell-specific hypothesis is that every AP in S has its
endpoint difference in D, including the zero difference. -/
theorem roth_of_avoiding_slope {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (N K : ℕ) (S D : Finset G) (a : G)
    (ha : ∀ d ∈ Finset.Ico 1 N, d • a ∉ D)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y → z - x ∈ D)
    (h : Fintype.card G * K ≤ N * S.card) :
    K ≤ rothNumberNat N := by
  classical
  obtain ⟨b, hb⟩ := shift_large_preimage (Finset.range N) S
    (fun n => n • a) K (by simpa using h)
  let P := (Finset.range N).filter fun i => i • a + b ∈ S
  have havoid (x z : ℕ) (hxz : x < z) (hz : z < N) :
      (z • a + b) - (x • a + b) ∉ D := by
    have hd : z - x ∈ Finset.Ico 1 N := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have he : z • a = x • a + (z - x) • a := by
      calc
        z • a = (x + (z - x)) • a := congrArg (fun n : ℕ => n • a) (by omega)
        _ = _ := add_nsmul a x (z - x)
    have hdif : (z • a + b) - (x • a + b) = (z - x) • a := by rw [he]; abel
    rw [hdif]
    exact ha _ hd
  have hfree : ThreeAPFree (P : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro x hx y hy z hz hAP
    have hx' := Finset.mem_filter.mp (show x ∈ P from hx)
    have hy' := Finset.mem_filter.mp (show y ∈ P from hy)
    have hz' := Finset.mem_filter.mp (show z ∈ P from hz)
    have he : (x • a + b) + (z • a + b) = (y • a + b) + (y • a + b) := by
      calc
        _ = (x + z) • a + (b + b) := by rw [add_nsmul]; abel
        _ = _ := by rw [hAP, add_nsmul]; abel
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact havoid x z hlt (Finset.mem_range.mp hz'.1)
        (hS _ hx'.2 _ hy'.2 _ hz'.2 he)
    · exact havoid z x hgt (Finset.mem_range.mp hx'.1)
        (hS _ hz'.2 _ hy'.2 _ hx'.2 (by simpa [add_comm] using he))
  exact le_trans hb (ThreeAPFree.le_rothNumberNat P hfree
    (fun _ hx => Finset.mem_range.mp (Finset.mem_filter.mp hx).1) rfl)



/-- Pigeonhole selection of a potential shell of width w.
No concentration theorem or probability measure is required. -/
theorem exists_potential_shell {G : Type*} (S : Finset G)
    (F : G → ℝ) (w : ℝ) (L K : ℕ)
    (hw : 0 < w) (hL : 0 < L)
    (hF : ∀ x ∈ S, 0 ≤ F x ∧ F x < (L : ℝ) * w)
    (hcard : L * K ≤ S.card) :
    ∃ T : Finset G, T ⊆ S ∧ K ≤ T.card ∧
      ∃ b : ℝ, ∀ x ∈ T, b ≤ F x ∧ F x ≤ b + w := by
  classical
  let label : G → ℕ := fun x => ⌊F x / w⌋₊
  have hmap : ∀ x ∈ S, label x ∈ Finset.range L := by
    intro x hx
    apply Finset.mem_range.mpr
    exact (Nat.floor_lt (div_nonneg (hF x hx).1 hw.le)).2
      ((div_lt_iff₀ hw).2 (hF x hx).2)
  have hn : (Finset.range L).Nonempty :=
    ⟨0, Finset.mem_range.mpr hL⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    hmap hn (by simpa using hcard)
  let T := S.filter fun x => label x = j
  refine ⟨T, Finset.filter_subset _ _, hj, (j : ℝ) * w, ?_⟩
  intro x hx
  have hm := Finset.mem_filter.mp (show x ∈ T from hx)
  have hnon := div_nonneg (hF x hm.1).1 hw.le
  have hlo := Nat.floor_le hnon
  have hhi := Nat.lt_floor_add_one (F x / w)
  -- Keep the membership and the index equality separate.
  have he : ⌊F x / w⌋₊ = j := (Finset.mem_filter.mp (show x ∈ T from hx)).2
  rw [he] at hlo hhi
  refine ⟨(le_div_iff₀ hw).mp hlo, ?_⟩
  have hh := (div_lt_iff₀ hw).mp hhi
  linarith

/-- A single transfer lemma combining slope avoidance, shift averaging,
and the exact Mathlib Roth-number statement. -/
theorem roth_of_short_differences {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (N K : ℕ) (S D : Finset G)
    (e : ℕ → G ≃ G)
    (he : ∀ d ∈ Finset.Ico 1 N, ∀ a : G, e d a = d • a)
    (hD : N * D.card < Fintype.card G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y → z - x ∈ D)
    (hK : Fintype.card G * K ≤ N * S.card) :
    K ≤ rothNumberNat N := by
  obtain ⟨a, ha⟩ := exists_avoiding_slope N D e he hD
  exact roth_of_avoiding_slope N K S D a ha hS hK


/-! Count short differences by a coordinate box.  For the leading
exponential constant this weaker estimate suffices; ball-volume
estimates are not needed. -/

def shortResidues (p R : ℕ) : Finset (ZMod p) :=
  (Finset.range (2 * R + 1)).image (fun i : ℕ =>
    (((i : ℤ) - (R : ℤ)) : ZMod p))

lemma mem_shortResidues {p R : ℕ} {x : ℤ}
    (hl : -(R : ℤ) ≤ x) (hr : x ≤ (R : ℤ)) :
    (x : ZMod p) ∈ shortResidues p R := by
  have hn : 0 ≤ x + (R : ℤ) := by omega
  let i := (x + (R : ℤ)).toNat
  have hi : (i : ℤ) = x + (R : ℤ) := Int.toNat_of_nonneg hn
  have hib : i < 2 * R + 1 := by omega
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_range.mpr hib, ?_⟩
  have he : (i : ℤ) - (R : ℤ) = x := by omega
  simpa only [Int.cast_sub] using congrArg (fun a : ℤ => (a : ZMod p)) he

lemma shortResidues_card (p R : ℕ) :
    (shortResidues p R).card ≤ 2 * R + 1 := by
  unfold shortResidues
  exact Finset.card_image_le.trans (by simp)

def shortBox (p m R : ℕ) : Finset (Fin m → ZMod p × ZMod p) :=
  Fintype.piFinset fun _ => (shortResidues p R).product (shortResidues p R)

lemma shortBox_card (p m R : ℕ) :
    (shortBox p m R).card ≤ ((2 * R + 1) * (2 * R + 1)) ^ m := by
  unfold shortBox
  rw [Fintype.card_piFinset_const]
  have hc : ((shortResidues p R).product (shortResidues p R)).card =
      (shortResidues p R).card * (shortResidues p R).card :=
    Finset.card_product _ _
  rw [hc]
  exact Nat.pow_le_pow_left
    (Nat.mul_le_mul (shortResidues_card p R) (shortResidues_card p R)) _

lemma normalized_square_to_int_bound {p R : ℕ} (hp : 0 < p)
    {x : ℤ} (h : ((x : ℝ) / (p : ℝ))^2 ≤ ((R : ℝ) / (p : ℝ))^2) :
    -(R : ℤ) ≤ x ∧ x ≤ (R : ℤ) := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hR : 0 ≤ (R : ℝ) / (p : ℝ) := by positivity
  have hright : (x : ℝ) / (p : ℝ) ≤ (R : ℝ) / (p : ℝ) := by
    by_contra hn
    have hpos : 0 < (x : ℝ) / (p : ℝ) - (R : ℝ) / (p : ℝ) := by linarith
    have hpos' : 0 < (x : ℝ) / (p : ℝ) + (R : ℝ) / (p : ℝ) := by linarith
    nlinarith [mul_pos hpos hpos']
  have hleft : -((R : ℝ) / (p : ℝ)) ≤ (x : ℝ) / (p : ℝ) := by
    by_contra hn
    have hpos : 0 < -((x : ℝ) / (p : ℝ)) - (R : ℝ) / (p : ℝ) := by linarith
    have hpos' : 0 < -((x : ℝ) / (p : ℝ)) + (R : ℝ) / (p : ℝ) := by linarith
    nlinarith [mul_pos hpos hpos']
  have hrc := (div_le_div_iff_of_pos_right hp').mp hright
  rw [← neg_div] at hleft
  have hlc := (div_le_div_iff_of_pos_right hp').mp hleft
  exact ⟨by exact_mod_cast hlc, by exact_mod_cast hrc⟩

/-- Choose actual integer lifts and local real coordinates for each
point of the finite block.  Values outside the block are immaterial. -/
theorem finiteBlock_lift_functions (p : ℕ) [NeZero p] :
    ∃ X Y : ZMod p × ZMod p → ℤ,
      ∃ U : ZMod p × ZMod p → ℝ,
        ∀ v ∈ finiteBlock p,
          (X v : ZMod p) = v.1 ∧ (Y v : ZMod p) = v.2 ∧
            HasLocal ((X v : ℝ) / (p : ℝ)) ((Y v : ℝ) / (p : ℝ)) (U v) := by
  classical
  have h (v : ZMod p × ZMod p) :
      ∃ x y : ℤ, ∃ u : ℝ, v ∈ finiteBlock p →
        (x : ZMod p) = v.1 ∧ (y : ZMod p) = v.2 ∧
          HasLocal ((x : ℝ) / (p : ℝ)) ((y : ℝ) / (p : ℝ)) u := by
    by_cases hv : v ∈ finiteBlock p
    · have hm := Finset.mem_filter.mp (show v ∈ finiteBlock p from hv)
      obtain ⟨x, y, hx, hy, hB⟩ := hm.2
      obtain ⟨u, hu⟩ := block_hasLocal hB
      exact ⟨x, y, u, fun _ => ⟨hx, hy, hu⟩⟩
    · exact ⟨0, 0, 0, fun he => (hv he).elim⟩
  choose X Y U hXYU using h
  exact ⟨X, Y, U, hXYU⟩

/-- A thin shell of the actual product block has no progression whose
endpoint difference lies outside the counted short-coordinate box. -/
theorem product_shell_shortBox (p m R : ℕ) [NeZero p]
    (hp : 0 < p) (S : Finset (Fin m → ZMod p × ZMod p))
    (X Y : ZMod p × ZMod p → ℤ) (U : ZMod p × ZMod p → ℝ)
    (hX : ∀ v ∈ finiteBlock p,
      (X v : ZMod p) = v.1 ∧ (Y v : ZMod p) = v.2 ∧
        HasLocal ((X v : ℝ) / (p : ℝ)) ((Y v : ℝ) / (p : ℝ)) (U v))
    (hS : ∀ v ∈ S, ∀ i, v i ∈ finiteBlock p)
    (b w : ℝ) (hw : 2 * w ≤ ((R : ℝ) / (p : ℝ))^2)
    (hF : ∀ v ∈ S, b ≤ ∑ i, potential
      ((X (v i) : ℝ) / (p : ℝ)) (U (v i)) ∧
      (∑ i, potential ((X (v i) : ℝ) / (p : ℝ)) (U (v i))) ≤ b + w) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = y + y →
      z - x ∈ shortBox p m R := by
  classical
  intro x hx y hy z hz hAP
  have hx' (i : Fin m) := hX (x i) (hS x hx i)
  have hy' (i : Fin m) := hX (y i) (hS y hy i)
  have hz' (i : Fin m) := hX (z i) (hS z hz i)
  have hs (i : Fin m) : ∃ k : ℤ,
      2 * ((X (y i) : ℝ) / (p : ℝ)) =
        (X (x i) : ℝ) / (p : ℝ) + (X (z i) : ℝ) / (p : ℝ) + (k : ℝ) := by
    have he := congrFun hAP i
    have hh : (X (x i) : ZMod p) + (X (z i) : ZMod p) =
        2 * (X (y i) : ZMod p) := by
      rw [(hx' i).1, (hz' i).1, (hy' i).1, two_mul]
      exact congrArg Prod.fst he
    obtain ⟨k, hk⟩ := normalized_modular_AP hp hh
    refine ⟨-k, ?_⟩
    push_cast
    linarith
  have ha (i : Fin m) : ∃ j : ℤ,
      (Y (x i) : ℝ) / (p : ℝ) + (Y (z i) : ℝ) / (p : ℝ) -
        2 * ((Y (y i) : ℝ) / (p : ℝ)) = (j : ℝ) := by
    have he := congrFun hAP i
    apply normalized_modular_AP hp
    rw [(hx' i).2.1, (hz' i).2.1, (hy' i).2.1, two_mul]
    exact congrArg Prod.snd he
  choose k hk using hs
  choose j hj using ha
  let sx : Fin m → ℝ := fun i => (X (x i) : ℝ) / p
  let sy : Fin m → ℝ := fun i => (X (y i) : ℝ) / p
  let sz : Fin m → ℝ := fun i => (X (z i) : ℝ) / p
  let ax : Fin m → ℝ := fun i => (Y (x i) : ℝ) / p
  let ay : Fin m → ℝ := fun i => (Y (y i) : ℝ) / p
  let az : Fin m → ℝ := fun i => (Y (z i) : ℝ) / p
  have hsum := shell_endpoint_bound sx sy sz ax ay az
    (fun i => U (x i)) (fun i => U (y i)) (fun i => U (z i)) j k
    (fun i => (hx' i).2.2) (fun i => (hy' i).2.2) (fun i => (hz' i).2.2)
    hk hj b w (hF x hx).2 (hF y hy).1 (hF z hz).2
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : (sx i - sz i)^2 + (ax i - az i)^2 ≤
      ∑ i, ((sx i - sz i)^2 + (ax i - az i)^2) :=
    Finset.single_le_sum (f := fun a : Fin m => (sx a - sz a)^2 + (ax a - az a)^2)
      (fun a _ => by positivity) (Finset.mem_univ i)
  have hs2 : ((↑(X (z i) - X (x i) : ℤ) : ℝ) / p)^2 ≤
      ((R : ℝ) / (p : ℝ))^2 := by
    push_cast
    dsimp [sx, sz] at hi
    rw [sub_div]
    nlinarith [sq_nonneg (ax i - az i)]
  have ha2 : ((↑(Y (z i) - Y (x i) : ℤ) : ℝ) / p)^2 ≤
      ((R : ℝ) / (p : ℝ))^2 := by
    push_cast
    dsimp [ax, az] at hi
    rw [sub_div]
    nlinarith [sq_nonneg (sx i - sz i)]
  have hsB := normalized_square_to_int_bound hp hs2
  have haB := normalized_square_to_int_bound hp ha2
  have hsM := mem_shortResidues (p := p) hsB.1 hsB.2
  have haM := mem_shortResidues (p := p) haB.1 haB.2
  push_cast at hsM haM
  rw [(hz' i).1, (hx' i).1] at hsM
  rw [(hz' i).2.1, (hx' i).2.1] at haM
  exact Finset.mem_product.mpr ⟨hsM, haM⟩



/-! Specialize the transfer to the actual prime torus. -/

def slopePerm (p m d : ℕ) [Fact p.Prime] :
    (Fin m → ZMod p × ZMod p) ≃ (Fin m → ZMod p × ZMod p) :=
  if h : (d : ZMod p) = 0 then Equiv.refl _ else
    { toFun := fun a i => ((d : ZMod p) * (a i).1, (d : ZMod p) * (a i).2)
      invFun := fun a i => ((d : ZMod p)⁻¹ * (a i).1, (d : ZMod p)⁻¹ * (a i).2)
      left_inv := by
        intro a
        funext i
        apply Prod.ext <;> dsimp <;> rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
      right_inv := by
        intro a
        funext i
        apply Prod.ext <;> dsimp <;> rw [← mul_assoc, mul_inv_cancel₀ h, one_mul] }

lemma slopePerm_apply (p m N d : ℕ) [Fact p.Prime] (hN : N ≤ p)
    (hd : d ∈ Finset.Ico 1 N) (a : Fin m → ZMod p × ZMod p) :
    slopePerm p m d a = d • a := by
  have hd' := Finset.mem_Ico.mp hd
  have hn : (d : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff d p).mp hz
    have hle := Nat.le_of_dvd (show 0 < d by omega) hdiv
    omega
  unfold slopePerm
  rw [dite_eq_right hn]
  funext i
  apply Prod.ext <;> change (d : ZMod p) * _ = d • _ <;> rw [nsmul_eq_mul]

/-- Finite-parameter construction: all density, shell, slope and AP
arguments are internal.  Only numerical inequalities on the parameters
remain as hypotheses, suitable for the final asymptotic optimization. -/
theorem roth_finite_parameters (p m R N L J K : ℕ) [Fact p.Prime]
    (hN : N ≤ p) (hp : 2400000 ≤ p) (hL : 0 < L)
    (w : ℝ) (hw : 0 < w)
    (hwR : 2 * w ≤ ((R : ℝ) / (p : ℝ))^2)
    (hwidth : (m : ℝ) * 1000001 < (L : ℝ) * w)
    (hD : N * ((2 * R + 1) * (2 * R + 1)) ^ m < (p * p)^m)
    (hJ : L * J ≤ (finiteBlock p).card ^ m)
    (hK : (p * p)^m * K ≤ N * J) :
    K ≤ rothNumberNat N := by
  classical
  have hp' : 0 < p := by omega
  obtain ⟨X, Y, U, hX⟩ := finiteBlock_lift_functions p
  let B : Finset (Fin m → ZMod p × ZMod p) :=
    Fintype.piFinset fun _ => finiteBlock p
  let F : (Fin m → ZMod p × ZMod p) → ℝ :=
    fun v => ∑ i, potential ((X (v i) : ℝ) / (p : ℝ)) (U (v i))
  have hB : B.card = (finiteBlock p).card ^ m := by
    exact Fintype.card_piFinset_const _ _
  have hF (v : Fin m → ZMod p × ZMod p) (hv : v ∈ B) :
      0 ≤ F v ∧ F v < (L : ℝ) * w := by
    have hm := Fintype.mem_piFinset.mp hv
    have hb (i : Fin m) := potential_bounds ((hX (v i) (hm i)).2.2)
    constructor
    · exact Finset.sum_nonneg (fun i _ => (hb i).1)
    · have hsum : F v ≤ ∑ _i : Fin m, (1000001 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hb i).2
      have hsum' : F v ≤ (m : ℝ) * 1000001 := by
        simpa using hsum
      exact lt_of_le_of_lt hsum' hwidth
  obtain ⟨S, hSB, hJS, b, hS⟩ := exists_potential_shell B F w L J hw hL hF
    (by rw [hB]; exact hJ)
  have hshort := product_shell_shortBox p m R hp' S X Y U hX
    (fun v hv i => Fintype.mem_piFinset.mp (hSB hv) i) b w hwR hS
  have hcardG : Fintype.card (Fin m → ZMod p × ZMod p) = (p * p)^m := by
    simp [Fintype.card_prod, ZMod.card]
  apply roth_of_short_differences N K S (shortBox p m R) (fun d => slopePerm p m d)
  · exact fun d hd a => slopePerm_apply p m N d hN hd a
  · rw [hcardG]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left N (shortBox_card p m R)) hD
  · exact hshort
  · rw [hcardG]
    exact le_trans hK (Nat.mul_le_mul_left N hJS)



/-! Eliminate the prime modulus and auxiliary shell parameters. -/

lemma div_mul_bounds (a b : ℕ) (hb : 0 < b) :
    a / b * b ≤ a ∧ a < a / b * b + b := by
  have he := Nat.div_add_mod a b
  have hr := Nat.mod_lt a hb
  rw [Nat.mul_comm b (a / b)] at he
  omega

/-- A dimension-dependent lower bound involving only integer parameters
N, m and t. The additive 2 accounts for two finite pigeonhole roundings.
No asymptotic hypothesis or unproved geometric premise is present. -/
theorem roth_integer_parameters (N m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (hNt : N < (t * t)^m) :
    (N : ℝ) * (73 / 250 : ℝ)^m <
      (128 : ℝ) * ((m : ℝ) * 1000001 + 1) * (t : ℝ)^2 *
        ((rothNumberNat N : ℝ) + 2) := by
  obtain ⟨p, hpbound, hprime⟩ := Nat.exists_infinite_primes
    (max (max N 2400000) (8 * t))
  let _ : Fact p.Prime := ⟨hprime⟩
  have hN : N ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hpbound
  have hp : 2400000 ≤ p :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hpbound
  have hpt : 8 * t ≤ p := le_trans (le_max_right _ _) hpbound
  have hp0 : 0 < p := by omega
  let R := p / (4 * t)
  let L := 128 * (m * 1000001 + 1) * t^2
  let G := (p * p)^m
  let A := (finiteBlock p).card^m
  let J := A / L
  let K := (N * J) / G
  let w : ℝ := 1 / (128 * (t : ℝ)^2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hR := div_mul_bounds p (4 * t) (by omega)
  have hrlo : p ≤ 8 * t * R := by
    change R * (4 * t) ≤ p ∧ p < R * (4 * t) + 4 * t at hR
    nlinarith [hR.2, hpt]
  have hrt : (2 * R + 1) * t ≤ p := by
    change R * (4 * t) ≤ p ∧ p < R * (4 * t) + 4 * t at hR
    nlinarith [hR.1, hpt]
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hw : 0 < w := by dsimp [w]; positivity
  have hwR : 2 * w ≤ ((R : ℝ) / (p : ℝ))^2 := by
    have hr : (p : ℝ) ≤ 8 * (t : ℝ) * (R : ℝ) := by exact_mod_cast hrlo
    have hdiv : 1 / (8 * (t : ℝ)) ≤ (R : ℝ) / (p : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 8 * (t : ℝ)) hp').2
      linarith
    have hs := mul_le_mul hdiv hdiv (by positivity) (by positivity)
    calc
      2 * w = (1 / (8 * (t : ℝ))) * (1 / (8 * (t : ℝ))) := by
        dsimp [w]
        field_simp
        ring
      _ ≤ ((R : ℝ) / (p : ℝ))^2 := by simpa [pow_two] using hs
  have hwidth : (m : ℝ) * 1000001 < (L : ℝ) * w := by
    have he : (L : ℝ) * w = (m : ℝ) * 1000001 + 1 := by
      dsimp [L, w]
      push_cast
      field_simp
    linarith
  have hD : N * ((2 * R + 1) * (2 * R + 1))^m < G := by
    have hprod := Nat.mul_le_mul hrt hrt
    have hbase : (t * t) * ((2 * R + 1) * (2 * R + 1)) ≤ p * p := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod
    calc
      _ < (t * t)^m * ((2 * R + 1) * (2 * R + 1))^m :=
        Nat.mul_lt_mul_of_pos_right hNt (by positivity)
      _ = ((t * t) * ((2 * R + 1) * (2 * R + 1)))^m := by simp only [mul_pow]
      _ ≤ G := Nat.pow_le_pow_left hbase m
  have hJ := div_mul_bounds A L hL
  have hK := div_mul_bounds (N * J) G hG
  have hJ' : L * J ≤ A := by simpa [J, Nat.mul_comm] using hJ.1
  have hK' : G * K ≤ N * J := by simpa [K, Nat.mul_comm] using hK.1
  have hr := roth_finite_parameters p m R N L J K hN hp hL w hw hwR hwidth hD hJ' hK'
  have hNG : N ≤ G := by
    have hpp : p ≤ p * p := by nlinarith
    have hpow : p * p ≤ (p * p)^m := by
      simpa using (pow_le_pow_right' (show 1 ≤ p * p by exact Nat.succ_le_of_lt (Nat.mul_pos hp0 hp0))
        (show 1 ≤ m by omega))
    exact hN.trans (hpp.trans hpow)
  have hden := finite_block_density p hp
  have hden' : (73 / 250 : ℝ) * ((p : ℝ) * p) ≤ ((finiteBlock p).card : ℝ) := by
    have hd : 73 * (p : ℝ)^2 ≤ 250 * ((finiteBlock p).card : ℝ) := by exact_mod_cast hden
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (73 / 250 : ℝ) * ((p : ℝ) * p)) hden' m
  have hAG : (73 / 250 : ℝ)^m * (G : ℝ) ≤ (A : ℝ) := by
    dsimp [A, G]
    push_cast
    rw [← mul_pow]
    exact hpow
  have hA : (A : ℝ) < (L : ℝ) * ((J : ℝ) + 1) := by
    have hh : (A : ℝ) < (J : ℝ) * (L : ℝ) + (L : ℝ) := by
      exact_mod_cast hJ.2
    nlinarith
  have hNJ : (N : ℝ) * (J : ℝ) < (G : ℝ) * ((K : ℝ) + 1) := by
    have hh : (N : ℝ) * (J : ℝ) < (K : ℝ) * (G : ℝ) + (G : ℝ) := by
      exact_mod_cast hK.2
    nlinarith
  have hNG' : (N : ℝ) ≤ (G : ℝ) := by exact_mod_cast hNG
  have hKr : (K : ℝ) ≤ (rothNumberNat N : ℝ) := by exact_mod_cast hr
  have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
  have hGp : 0 < (G : ℝ) := by exact_mod_cast hG
  have hnp : 0 ≤ (N : ℝ) := by positivity
  have hN0 : N = 0 ∨ 0 < N := by omega
  rcases hN0 with hzero | hpos
  · subst N
    simp only [Nat.cast_zero, zero_mul]
    positivity
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hpos
  have hmain : (N : ℝ) * (73 / 250 : ℝ)^m * (G : ℝ) <
      (L : ℝ) * ((rothNumberNat N : ℝ) + 2) * (G : ℝ) := by
    calc
      _ ≤ (N : ℝ) * (A : ℝ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hAG hnp
      _ < (N : ℝ) * ((L : ℝ) * ((J : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hA hNp
      _ = (L : ℝ) * ((N : ℝ) * (J : ℝ) + (N : ℝ)) := by ring
      _ < (L : ℝ) * ((G : ℝ) * ((K : ℝ) + 2)) := by
        apply mul_lt_mul_of_pos_left _ hLp
        nlinarith
      _ ≤ (L : ℝ) * ((G : ℝ) * ((rothNumberNat N : ℝ) + 2)) := by
        gcongr
      _ = _ := by ring
  have hfinal : (N : ℝ) * (73 / 250 : ℝ)^m <
      (L : ℝ) * ((rothNumberNat N : ℝ) + 2) := by
    by_contra hn
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right (le_of_not_gt hn) hGp.le)) hmain
  dsimp [L] at hfinal
  push_cast at hfinal
  exact hfinal



/-! Analytic optimization of the integer-parameter estimate. -/

/-- Eliminate the integer radius parameter by rounding an exponential
upwards. All dependence on dimension is retained explicitly. -/
theorem roth_exp_parameters (N m : ℕ) (hN : 1 ≤ N) (hm : 0 < m) :
    (N : ℝ) * Real.exp (-((m : ℝ) * Real.log (250 / 73) +
      Real.log (N : ℝ) / (m : ℝ))) <
      512 * ((m : ℝ) * 1000001 + 1) * ((rothNumberNat N : ℝ) + 2) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let v : ℝ := Real.log (N : ℝ) / (2 * (m : ℝ))
  let E : ℝ := Real.exp v
  have hv : 0 ≤ v := div_nonneg (Real.log_nonneg hn1) (by positivity)
  have hE : 1 ≤ E := Real.one_le_exp hv
  let t : ℕ := ⌊E⌋₊ + 1
  have ht : 0 < t := by dsimp [t]; omega
  have htl : E < (t : ℝ) := by
    dsimp [t]
    push_cast
    exact Nat.lt_floor_add_one E
  have htu : (t : ℝ) ≤ 2 * E := by
    have hh := Nat.floor_le (show 0 ≤ E by linarith)
    dsimp [t]
    push_cast
    linarith
  have hEpow : (E * E)^m = (N : ℝ) := by
    dsimp [E]
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    have he : (m : ℝ) * (v + v) = Real.log (N : ℝ) := by
      dsimp [v]
      field_simp
      ring
    rw [he, Real.exp_log hNp]
  have hbase : E * E < (t : ℝ) * (t : ℝ) := by
    nlinarith [mul_pos (show 0 < (t : ℝ) - E by linarith)
      (show 0 < (t : ℝ) + E by linarith)]
  have hNt' : (N : ℝ) < ((t : ℝ) * (t : ℝ))^m := by
    rw [← hEpow]
    exact pow_lt_pow_left₀ hbase (by positivity) (Nat.ne_of_gt hm)
  have hNt : N < (t * t)^m := by exact_mod_cast hNt'
  have h := roth_integer_parameters N m t hm ht hNt
  have ht2 : (t : ℝ)^2 ≤ 4 * Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
    have hh := mul_le_mul htu htu (by positivity) (by positivity)
    have he : E * E = Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      dsimp [v]
      ring
    nlinarith
  let a : ℝ := Real.log (250 / 73)
  have hden : Real.exp (-a) = (73 / 250 : ℝ) := by
    dsimp [a]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 250 / 73)]
    norm_num
  have hpow : (73 / 250 : ℝ)^m = Real.exp (-((m : ℝ) * a)) := by
    rw [← hden, ← Real.exp_nat_mul]
    congr 1
    ring
  have hnon : 0 ≤ (128 : ℝ) * ((m : ℝ) * 1000001 + 1) *
      ((rothNumberNat N : ℝ) + 2) := by positivity
  have hh : (N : ℝ) * Real.exp (-((m : ℝ) * a)) <
      512 * ((m : ℝ) * 1000001 + 1) * ((rothNumberNat N : ℝ) + 2) *
      Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
    rw [hpow] at h
    calc
      _ < 128 * ((m : ℝ) * 1000001 + 1) * (t : ℝ)^2 *
          ((rothNumberNat N : ℝ) + 2) := h
      _ = (128 * ((m : ℝ) * 1000001 + 1) *
          ((rothNumberNat N : ℝ) + 2)) * (t : ℝ)^2 := by ring
      _ ≤ (128 * ((m : ℝ) * 1000001 + 1) *
          ((rothNumberNat N : ℝ) + 2)) *
          (4 * Real.exp (Real.log (N : ℝ) / (m : ℝ))) :=
        mul_le_mul_of_nonneg_left ht2 hnon
      _ = _ := by ring
  have hpos := Real.exp_pos (-(Real.log (N : ℝ) / (m : ℝ)))
  have hmul := mul_lt_mul_of_pos_right hh hpos
  have hcancel : Real.exp (Real.log (N : ℝ) / (m : ℝ)) *
      Real.exp (-(Real.log (N : ℝ) / (m : ℝ))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hleft : Real.exp (-((m : ℝ) * a)) *
      Real.exp (-(Real.log (N : ℝ) / (m : ℝ))) =
      Real.exp (-((m : ℝ) * a + Real.log (N : ℝ) / (m : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, hleft, hcancel, mul_one, a] using hmul

/-- Optimize the dimension with one-sided rounding. This formulation
exhibits the improved leading coefficient without any numerical log
approximation. The polynomial factor and +2 remain to be absorbed. -/
theorem roth_sqrt_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.exp (-(2 * Real.sqrt (Real.log (250 / 73)) *
      Real.sqrt (Real.log (N : ℝ)) + Real.log (250 / 73))) <
      512 * (1000001 * (Real.sqrt (Real.log (N : ℝ)) /
        Real.sqrt (Real.log (250 / 73)) + 1) + 1) *
        ((rothNumberNat N : ℝ) + 2) := by
  let a : ℝ := Real.log (250 / 73)
  let b : ℝ := Real.sqrt a
  let u : ℝ := Real.sqrt (Real.log (N : ℝ))
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hb : 0 < b := Real.sqrt_pos.2 ha
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hb2 : b^2 = a := Real.sq_sqrt ha.le
  have hu2 : u^2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hN))
  let m : ℕ := ⌊u / b⌋₊ + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hml : u / b < (m : ℝ) := by
    dsimp [m]
    push_cast
    exact Nat.lt_floor_add_one _
  have hmu : (m : ℝ) ≤ u / b + 1 := by
    have hh := Nat.floor_le (div_nonneg hu hb.le)
    dsimp [m]
    push_cast
    linarith
  have hmb : u ≤ (m : ℝ) * b := ((div_lt_iff₀ hb).mp hml).le
  have hma : (m : ℝ) * a ≤ b * u + a := by
    have hh := (le_div_iff₀ hb).mp (show (m : ℝ) - 1 ≤ u / b by linarith)
    calc
      (m : ℝ) * a = ((m : ℝ) - 1) * b * b + a := by rw [← hb2]; ring
      _ ≤ u * b + a := by
        linarith [mul_le_mul_of_nonneg_right hh hb.le]
      _ = b * u + a := by ring
  have hlog : Real.log (N : ℝ) / (m : ℝ) ≤ b * u := by
    apply (div_le_iff₀ hm').2
    calc
      Real.log (N : ℝ) = u * u := by rw [← hu2, pow_two]
      _ ≤ ((m : ℝ) * b) * u := mul_le_mul_of_nonneg_right hmb hu
      _ = b * u * (m : ℝ) := by ring
  have hopt : (m : ℝ) * a + Real.log (N : ℝ) / (m : ℝ) ≤
      2 * b * u + a := by linarith
  have h := roth_exp_parameters N m hN hm
  change (N : ℝ) * Real.exp (-((m : ℝ) * a +
    Real.log (N : ℝ) / (m : ℝ))) < _ at h
  change (N : ℝ) * Real.exp (-(2 * b * u + a)) <
    512 * (1000001 * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2)
  calc
    _ ≤ (N : ℝ) * Real.exp (-((m : ℝ) * a +
        Real.log (N : ℝ) / (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ < 512 * ((m : ℝ) * 1000001 + 1) * ((rothNumberNat N : ℝ) + 2) := h
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith

/-- Exact comparison of leading constants: the strict inequality does
not rely on a floating point evaluation of either logarithm. -/
theorem leading_constant_strict :
    2 * Real.sqrt (Real.log (250 / 73)) <
      2 * Real.sqrt (Real.log (24 / 7)) := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 250 / 73)
    (by norm_num : (250 / 73 : ℝ) < 24 / 7)
  have ha := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 250 / 73)
  have hs := Real.sqrt_lt_sqrt ha h
  linarith



/-! Final absorption of the polynomial factor, with an explicit
existence argument for the threshold. -/

lemma roth_at_least_one (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ rothNumberNat N := by
  apply ThreeAPFree.le_rothNumberNat ({0} : Finset ℕ)
  · simp
  · intro x hx
    have he : x = 0 := Finset.mem_singleton.mp hx
    omega
  · simp

lemma exp_dominates_linear (d M : ℝ) (hd : 0 < d) (_hM : 0 ≤ M) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → M * u ≤ Real.exp (d * u) := by
  let U := max 1 (4 * M / d^2)
  refine ⟨U, le_max_left _ _, ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : 0 ≤ u := by linarith
  have hU : 4 * M / d^2 ≤ u := le_trans (le_max_right _ _) hu
  have hcoef : 4 * M ≤ u * d^2 :=
    (div_le_iff₀ (by positivity : 0 < d^2)).mp hU
  have hquad : M * u ≤ (d * u / 2)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef hu0]
  have hv : 0 ≤ d * u / 2 := by positivity
  have he : d * u / 2 ≤ Real.exp (d * u / 2) := by
    linarith [Real.add_one_le_exp (d * u / 2)]
  have hs := mul_le_mul he he hv (Real.exp_pos _).le
  calc
    _ ≤ (d * u / 2)^2 := hquad
    _ ≤ Real.exp (d * u / 2) * Real.exp (d * u / 2) := by
      simpa only [pow_two] using hs
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Every coefficient strictly above the new leading coefficient
is attainable for all sufficiently large natural N. -/
theorem roth_eventual_of_constant (C : ℝ)
    (hC : 2 * Real.sqrt (Real.log (250 / 73)) < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ) := by
  let a : ℝ := Real.log (250 / 73)
  let b : ℝ := Real.sqrt a
  let d : ℝ := C - 2 * b
  let M : ℝ := 1536 * (1000001 * (1 / b + 1) + 1) * Real.exp a
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hb : 0 < b := Real.sqrt_pos.2 ha
  have hd : 0 < d := by dsimp [d, b, a]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨U, hU, hdom⟩ := exp_dominates_linear d M hd hM
  let N₀ : ℕ := ⌊Real.exp (U^2)⌋₊ + 1
  refine ⟨N₀, ?_⟩
  intro N hN
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  have hN1 : 1 ≤ N := by omega
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNN : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : Real.exp (U^2) < (N₀ : ℝ) := by
    dsimp [N₀]
    push_cast
    exact Nat.lt_floor_add_one _
  have hlog : U^2 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNp).2 (le_trans hexp.le hNN)
  let u : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hN1))
  have huU : U ≤ u := by
    by_contra hn
    have hpos : 0 < U - u := by linarith
    have hpos' : 0 < U + u := by linarith
    nlinarith [mul_pos hpos hpos']
  have hu1 : 1 ≤ u := le_trans hU huU
  have hD := hdom u huU
  have hr : 1 ≤ (rothNumberNat N : ℝ) := by exact_mod_cast roth_at_least_one N hN1
  have hr0 : 0 ≤ (rothNumberNat N : ℝ) := by positivity
  have hbase := roth_sqrt_bound N hN1
  change (N : ℝ) * Real.exp (-(2 * b * u + a)) <
    512 * (1000001 * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2) at hbase
  have hpoly : 512 * (1000001 * (u / b + 1) + 1) ≤
      512 * (1000001 * (1 / b + 1) + 1) * u := by
    have hquot : u / b = (1 / b) * u := by ring
    rw [hquot]
    nlinarith [mul_nonneg (show 0 ≤ (1 / b : ℝ) by positivity)
      (show 0 ≤ u - 1 by linarith)]
  have hbase' : (N : ℝ) * Real.exp (-(2 * b * u + a)) <
      1536 * (1000001 * (1 / b + 1) + 1) * u * (rothNumberNat N : ℝ) := by
    calc
      _ < 512 * (1000001 * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2) := hbase
      _ ≤ 512 * (1000001 * (1 / b + 1) + 1) * u *
          (3 * (rothNumberNat N : ℝ)) :=
        mul_le_mul hpoly (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hmult := mul_lt_mul_of_pos_right hbase' (Real.exp_pos a)
  have hleft : Real.exp (-(2 * b * u + a)) * Real.exp a =
      Real.exp (-(2 * b * u)) := by rw [← Real.exp_add]; congr 1; ring
  have hmain : (N : ℝ) * Real.exp (-(2 * b * u)) <
      Real.exp (d * u) * (rothNumberNat N : ℝ) := by
    calc
      _ = (N : ℝ) * (Real.exp (-(2 * b * u + a)) * Real.exp a) :=
        congrArg (fun x : ℝ => (N : ℝ) * x) hleft.symm
      _ = ((N : ℝ) * Real.exp (-(2 * b * u + a))) * Real.exp a :=
        (mul_assoc _ _ _).symm
      _ < (1536 * (1000001 * (1 / b + 1) + 1) * u *
          (rothNumberNat N : ℝ)) * Real.exp a := hmult
      _ = (M * u) * (rothNumberNat N : ℝ) := by dsimp [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD hr0
  change (N : ℝ) * Real.exp (-C * u) ≤ _
  have hc : Real.exp (-C * u) * Real.exp (d * u) =
      Real.exp (-(2 * b * u)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos (d * u))).mp
  calc
    _ = (N : ℝ) * (Real.exp (-C * u) * Real.exp (d * u)) := mul_assoc _ _ _
    _ = (N : ℝ) * Real.exp (-(2 * b * u)) :=
      congrArg (fun x : ℝ => (N : ℝ) * x) hc
    _ ≤ Real.exp (d * u) * (rothNumberNat N : ℝ) := hmain.le
    _ = _ := mul_comm _ _

/-- Target theorem: an unconditional strict improvement of the
leading exponential coefficient of the EHPS lower bound. -/
theorem erdos142_leading_constant_improvement :
    ∃ C : ℝ, 0 < C ∧ C < 2 * Real.sqrt (Real.log (24 / 7)) ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
          (rothNumberNat N : ℝ) := by
  let lo := 2 * Real.sqrt (Real.log (250 / 73))
  let hi := 2 * Real.sqrt (Real.log (24 / 7))
  have hlt : lo < hi := leading_constant_strict
  have hlo : 0 ≤ lo := by dsimp [lo]; positivity
  let C := (lo + hi) / 2
  have hC : lo < C := by dsimp [C]; linarith
  have hChi : C < hi := by dsimp [C]; linarith
  exact ⟨C, lt_of_le_of_lt hlo hC, hChi, roth_eventual_of_constant C hC⟩



/-! Independent statement-level bridge to the conventional interval
{1,...,N} and to an explicit arithmetic-progression condition. -/

theorem rothNumberNat_eq_interval (N : ℕ) :
    rothNumberNat N = addRothNumber (Finset.Icc 1 N) := by
  have he : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, addRothNumber_Ico]
  congr 1

/-- State the improvement directly in terms of finite subsets of the
conventional interval [1,N], without the extremal function or an
abstract AP-freeness predicate in the conclusion. -/
theorem erdos142_explicit_finite_sets :
    ∃ C : ℝ, 0 < C ∧ C < 2 * Real.sqrt (Real.log (24 / 7)) ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = y + y → x = z) ∧
          (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤ (A.card : ℝ) := by
  obtain ⟨C, hC0, hC, N₀, h⟩ := erdos142_leading_constant_improvement
  refine ⟨C, hC0, hC, N₀, ?_⟩
  intro N hN
  obtain ⟨A, hA, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx y hy z hz hAP
    exact threeAPFree_iff_eq_right.mp hfree hx hy hz hAP
  · rw [hcard, ← rothNumberNat_eq_interval]
    exact h N hN


/-- Cairn Commons submission target: the universal asymptotic bound,
expressed using only Mathlib objects and the explicit 3-AP condition. -/
theorem erdos142_cairn_target :
    ∀ C : ℝ, 2 * Real.sqrt (Real.log (250 / 73)) < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + z = y + y → x = z) ∧
          (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤ (A.card : ℝ) := by
  intro C hC
  obtain ⟨N₀, h⟩ := roth_eventual_of_constant C hC
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨A, hA, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx y hy z hz hAP
    exact threeAPFree_iff_eq_right.mp hfree hx hy hz hAP
  · rw [hcard, ← rothNumberNat_eq_interval]
    exact h N hN


end

end QuandleResearch.Erdos142
