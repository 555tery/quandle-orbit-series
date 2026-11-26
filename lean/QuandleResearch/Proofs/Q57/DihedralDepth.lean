import QuandleResearch.Proofs.Q57.Principal
import QuandleResearch.Checks.Q57StatementAudit
import Mathlib.Data.Set.Card

/-! The finite dihedral examples in BCNW Example 4.1. We use the
native Mathlib dihedral quandle and ZMod, and prove the needed lower
bound by computing the principal series at zero. The upper bound on
each individual fibre follows from finiteness, with no common bound. -/
namespace QuandleResearch.Q57
open BCNW Issue013

theorem OSBound_of_finite {X : Type*} [_root_.Quandle X]
    {s : Set X} (hs : s.Finite) : OSBound s s.ncard := by
  intro a ha
  have hsub (j : Nat) : a (j+1) ⊆ a j := by
    obtain ⟨x,hx,he⟩ := ha.2.2 j
    rw [he]
    exact orbitIn_subset _ _
  have hanti : Antitone a := antitone_nat_of_succ_le hsub
  have hfin (j : Nat) : (a j).Finite := hs.subset (by
    rw [← ha.1]
    exact hanti (Nat.zero_le j))
  by_contra! hn
  have hcard : ∀ j ≤ s.ncard+1, (a j).ncard + j ≤ s.ncard := by
    intro j
    induction j with
    | zero => intro _; simp [ha.1]
    | succ j ih =>
      intro hj
      have hlt : (a (j+1)).ncard < (a j).ncard :=
        Set.ncard_lt_ncard (lt_of_le_of_ne (hsub j) (Ne.symm (hn j (by omega)))) (hfin j)
      have := ih (by omega)
      omega
  have := hcard (s.ncard+1) le_rfl
  omega

theorem OSomega_of_finite {X : Type*} [_root_.Quandle X]
    {s : Set X} (hs : s.Finite) : OSomega s := by
  refine ⟨s.ncard+1, Nat.zero_lt_succ _, ?_⟩
  intro a ha
  obtain ⟨j,hj,he⟩ := OSBound_of_finite hs a ha
  exact ⟨j, Nat.le_trans hj (Nat.le_succ _), he⟩

namespace DihedralDepth
abbrev D (k : Nat) := Quandle.Dihedral (2^k)

def zero (k : Nat) : D k := (0 : ZMod (2^k))

def multiples (k : Nat) (d : ZMod (2^k)) : Set (D k) :=
  {z | ∃ t : ZMod (2^k), (z : ZMod (2^k)) = d*t}

theorem multiples_subrack (k : Nat) (d : ZMod (2^k)) :
    IsSubrack (multiples k d) := by
  rintro y ⟨i,hi⟩ x ⟨j,hj⟩
  constructor <;> refine ⟨2*i-j,?_⟩ <;>
    change 2*(y : ZMod (2^k))-(x : ZMod (2^k))=d*(2*i-j) <;>
    rw [hi,hj] <;> ring

theorem orbit_zero_multiples (k : Nat) (d : ZMod (2^k)) :
    orbitIn (multiples k d) (zero k) = multiples k (2*d) := by
  ext z
  constructor
  · intro hz
    have hw := (StatementAudit.walk_iff_orbit _ _ _).mpr hz.2
    clear hz
    induction hw with
    | nil => exact ⟨0, by change (0 : ZMod (2^k)) = 2*d*0; ring⟩
    | forward h hg ih =>
      obtain ⟨y,⟨i,hi⟩,rfl⟩ := hg
      obtain ⟨j,hj⟩ := ih
      refine ⟨i-j,?_⟩
      change 2*(y : ZMod (2^k))-_ = 2*d*(i-j)
      rw [hi,hj]
      ring
    | backward h hg ih =>
      obtain ⟨y,⟨i,hi⟩,rfl⟩ := hg
      obtain ⟨j,hj⟩ := ih
      refine ⟨i-j,?_⟩
      change 2*(y : ZMod (2^k))-_ = 2*d*(i-j)
      rw [hi,hj]
      ring
  · rintro ⟨t,ht⟩
    refine ⟨⟨2*t, by rw [ht]; ring⟩, (StatementAudit.walk_iff_orbit _ _ _).mp ?_⟩
    let y : D k := d*t
    have hw : StatementAudit.Walk ((_root_.Rack.act' : D k → Equiv.Perm (D k)) '' multiples k d)
        (zero k) ((_root_.Rack.act' y) (zero k)) :=
      StatementAudit.Walk.forward (g := Rack.act' y) StatementAudit.Walk.nil
        ⟨y,⟨t,rfl⟩,rfl⟩
    have he : (_root_.Rack.act' y) (zero k) = z := by
      change 2*(d*t)-0 = (z : ZMod (2^k))
      rw [ht]
      ring
    exact he ▸ hw

theorem principal_at_zero (k n : Nat) :
    principalSeries (Set.univ : Set (D k)) (zero k) n =
      multiples k ((2 : ZMod (2^k))^n) := by
  induction n with
  | zero =>
    ext z
    constructor
    · intro _
      exact ⟨z, by simp⟩
    · intro _
      exact Set.mem_univ _
  | succ n ih =>
    change orbitIn (principalSeries Set.univ (zero k) n) (zero k) =
      multiples k ((2 : ZMod (2^k))^(n+1))
    rw [ih,orbit_zero_multiples,pow_succ,mul_comm ((2 : ZMod (2^k))^n) 2]

/-- The component of order 2^(n+1) witnesses failure of the proposed
uniform bound n. It suffices to exhibit strictness at the last step;
earlier stabilization would persist. -/
theorem not_stable (n : Nat) : ¬ StableAt Set.univ (zero (n+1)) n := by
  intro he
  change principalSeries Set.univ (zero (n+1)) n =
    principalSeries Set.univ (zero (n+1)) (n+1) at he
  rw [principal_at_zero,principal_at_zero] at he
  let z : D (n+1) := (2 : ZMod (2^(n+1)))^n
  have hz : z ∈ multiples (n+1) ((2 : ZMod (2^(n+1)))^n) :=
    ⟨1, by simp [z]⟩
  rw [he] at hz
  obtain ⟨t,ht⟩ := hz
  have hzero : (2 : ZMod (2^(n+1)))^(n+1) = 0 := by
    have h : ((2^(n+1) : Nat) : ZMod (2^(n+1))) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl _)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have hz0 : (2 : ZMod (2^(n+1)))^n = 0 := by
    change (2 : ZMod (2^(n+1)))^n = (2 : ZMod (2^(n+1)))^(n+1)*t at ht
    simpa [hzero] using ht
  have hd : 2^(n+1) ∣ 2^n := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using hz0
  have hp : 0 < (2 : Nat)^n := pow_pos (by decide) _
  have hle := Nat.le_of_dvd hp hd
  rw [pow_succ] at hle
  omega

theorem not_bound (n : Nat) : ¬ OSBound (Set.univ : Set (D (n+1))) n := by
  intro hb
  exact not_stable n (stable_of_OSBound univ_isSubrack hb (Set.mem_univ (zero (n+1))))

end DihedralDepth
end QuandleResearch.Q57
