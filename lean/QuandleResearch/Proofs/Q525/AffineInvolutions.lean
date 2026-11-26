import QuandleResearch.Proofs.Q525.Consequences
import QuandleResearch.Proofs.Q525.Coefficients

/-! Elementary version of part B of Question 5.25.
The issue comment 7184606635 uses the affine semidirect product.
Here we work directly with its involutions, allowing the identity.
An element (u,s) corresponds to the affine map x ↦ (1+s)x+u.
Its square is the identity when s²=su=0 in characteristic two.
Conjugation is the explicit formula below. This slightly enlarges
the original union of conjugacy classes; all equal-s fibers remain
trivial, which is sufficient for the original boundedness question.
No nilpotency-class calculation is needed. -/
namespace QuandleResearch.Q525
open BCNW
variable {R : Type*} [CommRing R]

def Affine (R : Type*) [CommRing R] :=
  {p : R × R // p.2 * p.2 = 0 ∧ p.2 * p.1 = 0}

namespace Affine

def tr (a : Affine R) : R := a.val.1
def sc (a : Affine R) : R := a.val.2
theorem sc_sq (a : Affine R) : sc a * sc a = 0 := a.property.1
theorem sc_tr (a : Affine R) : sc a * tr a = 0 := a.property.2

theorem ext {a b : Affine R} (hu : tr a = tr b) (hs : sc a = sc b) : a = b :=
  Subtype.ext (Prod.ext hu hs)

instance [Finite R] : Finite (Affine R) :=
  Finite.of_injective (fun a : Affine R => a.val) Subtype.val_injective

def translation (u : R) : Affine R := ⟨(u,0), by simp⟩
def scalar (s : R) (hs : s * s = 0) : Affine R := ⟨(0,s), hs, by simp⟩

def op (a b : Affine R) : Affine R :=
  ⟨(tr b + sc a * tr b + sc b * tr a, sc b), sc_sq b, by
    change sc b * (tr b + sc a * tr b + sc b * tr a) = 0
    linear_combination (1 + sc a) * sc_tr b + tr a * sc_sq b⟩

@[simp] theorem tr_op (a b : Affine R) :
    tr (op a b) = tr b + sc a * tr b + sc b * tr a := rfl
@[simp] theorem sc_op (a b : Affine R) : sc (op a b) = sc b := rfl

theorem op_self (a : Affine R) : op a a = a := by
  apply ext
  · simp only [tr_op, sc_tr, add_zero]
  · rfl

theorem op_involutive (hc : ∀ x : R, x + x = 0) (a b : Affine R) :
    op a (op a b) = b := by
  apply ext
  · simp only [tr_op, sc_op]
    linear_combination hc (sc a * tr b + sc b * tr a) +
      tr b * sc_sq a + sc b * sc_tr a
  · rfl

theorem op_distrib (hc : ∀ x : R, x + x = 0) (a b c : Affine R) :
    op a (op b c) = op (op a b) (op a c) := by
  apply ext
  · simp only [tr_op, sc_op]
    linear_combination -hc (sc b * sc c * tr a)
  · rfl

def quandle (hc : ∀ x : R, x + x = 0) : _root_.Quandle (Affine R) where
  act := op
  self_distrib := by intro a b c; exact op_distrib hc a b c
  invAct := op
  left_inv := op_involutive hc
  right_inv := op_involutive hc
  fix := op_self _

/-- Every orbit has constant scalar coordinate. -/
theorem orbit_sc (hc : ∀ x : R, x + x = 0) (a b : Affine R) :
    letI := quandle hc
    b ∈ orbitIn Set.univ a → sc b = sc a := by
  letI := quandle hc
  intro h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h.2
  change g.val a = b at hg
  have hall : ∀ x : Affine R, sc (g.val x) = sc x := by
    have hg' := g.property
    change g.val ∈ Subgroup.closure
      ((_root_.Rack.act' : Affine R → Equiv.Perm (Affine R)) '' Set.univ) at hg'
    induction hg' using Subgroup.closure_induction with
    | mem p hp =>
      obtain ⟨y, _, rfl⟩ := hp
      intro x
      rfl
    | one => intro x; rfl
    | mul p q hp hq ihp ihq =>
      intro x
      change sc (p (q x)) = sc x
      exact (ihp (q x)).trans (ihq x)
    | inv p hp ih =>
      intro x
      have h := ih (p.symm x)
      simpa using h.symm
  rw [← hg]
  exact hall a

/-- Equal-scalar fibers are trivial, hence so are all inner orbits. -/
theorem trivial_orbits (hc : ∀ x : R, x + x = 0) :
    letI := quandle hc
    ∀ x : Affine R, TrivialOn (orbitIn Set.univ x) := by
  letI := quandle hc
  intro x a ha b hb
  have he : sc a = sc b := (orbit_sc hc x a ha).trans (orbit_sc hc x b hb).symm
  change op a b = b
  apply ext
  · simp only [tr_op]
    rw [he, sc_tr b, add_zero, ← he, sc_tr a, add_zero]
  · rfl

/-- The difference of the two translations is multiplied by the scalar
parameter of the next right operand, while their scalar coordinates
become equal. This avoids the Inn-nilpotency criterion entirely. -/
theorem fold_difference (hc : ∀ x : R, x + x = 0)
    (cs : List (Affine R)) (a b : Affine R) (he : sc a = sc b) :
    letI := quandle hc
    tr (leftFold a cs) - tr (leftFold b cs) =
      (tr a - tr b) * (cs.map sc).prod := by
  letI := quandle hc
  induction cs generalizing a b with
  | nil => simp [leftFold]
  | cons c cs ih =>
    change tr (leftFold (op a c) cs) - tr (leftFold (op b c) cs) =
      (tr a - tr b) * (sc c * (cs.map sc).prod)
    rw [ih (op a c) (op b c) rfl]
    simp only [tr_op, he]
    ring

/-- A square-zero word of nonzero product supplies a direct violation
of n-reductivity of this finite affine quandle. -/
theorem nonreductive_witness (hc : ∀ x : R, x + x = 0) (n : Nat)
    (hw : SquareZeroWord R n) :
    letI := quandle hc
    ∃ (a b : Affine R) (cs : List (Affine R)),
      cs.length = n ∧ leftFold a cs ≠ leftFold b cs := by
  letI := quandle hc
  obtain ⟨ts, hlen, hsq, hp⟩ := hw
  let cs := ts.attach.map (fun t => scalar t.val (hsq t.val t.property))
  have hmap : cs.map sc = ts := by
    simp [cs, sc, scalar, List.map_map]
  refine ⟨translation 1, translation 0, cs, by simp [cs, hlen], ?_⟩
  intro h
  have hd := fold_difference hc cs (translation 1) (translation 0) rfl
  rw [h, sub_self, hmap] at hd
  exact hp (by simpa [tr, translation] using hd.symm)

end Affine

/-- The full second negative answer, via the finite affine model.
Only standard ring identities and the dual-number construction above
are used. -/
theorem partB : QuandleResearch.Issue014.negativeB := by
  apply QuandleResearch.Issue014.negativeB_of_unboundedIAt 2 (by decide)
  apply QuandleResearch.Issue014.unboundedIAt_two_of_trivial_orbit_witnesses
  intro n hn
  obtain ⟨R, r, h⟩ := coefficient_exists n
  letI := r
  obtain ⟨hf, hc, hw⟩ := h
  letI : Finite R := hf
  exact ⟨Affine R, Affine.quandle hc, inferInstance,
    Affine.trivial_orbits hc, Affine.nonreductive_witness hc n hw⟩

#print axioms partB
end QuandleResearch.Q525
