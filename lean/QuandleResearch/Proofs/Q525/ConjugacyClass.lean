import QuandleResearch.Proofs.Q525.Consequences
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Action.End

/-! Group-to-quandle bridge for the elementary 3×3 model.
The class is a native Mathlib conjugation orbit. The only tower is
the closure of successive conjugate sets; no exact cardinalities,
central-series calculations, or external results are needed. -/
namespace QuandleResearch.Q525
open BCNW
variable {G : Type*} [Group G]

abbrev Class (a : G) := ↥(MulAction.orbit (ConjAct G) a)

namespace Class

def anchor (a : G) : Class a := ⟨a, MulAction.mem_orbit_self a⟩

instance {a : G} : _root_.Quandle (Class a) where
  act x y := ConjAct.toConjAct x.val • y
  invAct x y := ConjAct.toConjAct x.val⁻¹ • y
  self_distrib := by
    intro x y z
    apply Subtype.ext
    change x.val * (y.val * z.val * y.val⁻¹) * x.val⁻¹ =
      (x.val * y.val * x.val⁻¹) * (x.val * z.val * x.val⁻¹) *
        (x.val * y.val * x.val⁻¹)⁻¹
    group
  left_inv x y := by
    apply Subtype.ext
    change x.val⁻¹ * (x.val * y.val * x.val⁻¹) * (x.val⁻¹)⁻¹ = y.val
    group
  right_inv x y := by
    apply Subtype.ext
    change x.val * (x.val⁻¹ * y.val * (x.val⁻¹)⁻¹) * x.val⁻¹ = y.val
    group
  fix := by
    intro x
    apply Subtype.ext
    change x.val * x.val * x.val⁻¹ = x.val
    group

/-- The conjugation representation on the ambient conjugacy class. -/
abbrev rho (a : G) : G →* Equiv.Perm (Class a) :=
  (MulAction.toPermHom (ConjAct G) (Class a)).comp
    ConjAct.toConjAct.toMonoidHom

@[simp] theorem rho_val {a : G} (g : G) (x : Class a) :
    (rho a g x).val = g * x.val * g⁻¹ := rfl

theorem rho_eq_translation {a : G} (x : Class a) :
    rho a x.val = _root_.Rack.act' x := by
  ext y
  rfl

theorem translationGroup_eq_map {a : G} (s : Set (Class a)) :
    translationGroup s =
      (Subgroup.closure (Subtype.val '' s)).map (rho a) := by
  rw [Subgroup.map_closure]
  congr 1
  rw [Set.image_image]
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,rho_eq_translation x⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(rho_eq_translation x).symm⟩

/-- All elements of the conjugacy class are involutions if a is. -/
theorem square_eq_one {a : G} (ha : a*a = 1) (x : Class a) :
    x.val * x.val = 1 := by
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp x.property
  change ConjAct.ofConjAct g * a * (ConjAct.ofConjAct g)⁻¹ = x.val at hg
  rw [← hg]
  calc
    _ = ConjAct.ofConjAct g * (a*a) * (ConjAct.ofConjAct g)⁻¹ := by group
    _ = 1 := by rw [ha]; simp

/-- Pairwise fourth powers imply the LR₂ identity for the class of an
involution. This is the only local-reductivity group identity needed. -/
theorem locallyReductiveTwo {a : G} (ha : a*a = 1)
    (hp : ∀ x y : Class a, (x.val*y.val)^4 = 1) :
    LocallyReductive (X := Class a) 2 := by
  intro x y
  have hx : x.val⁻¹ = x.val := by
    apply inv_eq_of_mul_eq_one_right
    exact square_eq_one ha x
  have hy : y.val⁻¹ = y.val := by
    apply inv_eq_of_mul_eq_one_right
    exact square_eq_one ha y
  apply Subtype.ext
  change (x.val*y.val*x.val⁻¹)*y.val*(x.val*y.val*x.val⁻¹)⁻¹ = y.val
  have h := hp x y
  have hc : x.val*y.val*x.val*y.val =
      y.val*x.val*y.val*x.val := by
    calc
      _ = (x.val*y.val)^2 := by group
      _ = ((x.val*y.val)^2)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← pow_add]
        exact h
      _ = _ := by simp [pow_two, hx, hy, mul_assoc]
  rw [hx]
  have hh : x.val*y.val*x.val*y.val =
      y.val*(x.val*y.val*x.val) := by simpa [mul_assoc] using hc
  exact (mul_inv_eq_iff_eq_mul).2 hh

end Class

/-- Native conjugation, restricted to a subgroup of the ambient group. -/
def conjugatesIn (H : Subgroup G) (a : G) : Set G :=
  {y | ∃ g : H, g.val * a * g.val⁻¹ = y}

def next (a : G) (H : Subgroup G) : Subgroup G :=
  Subgroup.closure (conjugatesIn H a)

def tower (a : G) : Nat → Subgroup G
  | 0 => ⊤
  | n+1 => next a (tower a n)

theorem self_mem_next (a : G) (H : Subgroup G) : a ∈ next a H :=
  Subgroup.subset_closure ⟨1, by simp⟩

theorem self_mem_tower (a : G) (n : Nat) : a ∈ tower a n := by
  cases n with
  | zero => exact Subgroup.mem_top a
  | succ n => exact self_mem_next a (tower a n)

theorem next_le {a : G} {H : Subgroup G} (ha : a ∈ H) : next a H ≤ H := by
  apply (Subgroup.closure_le H).mpr
  rintro y ⟨g,rfl⟩
  exact H.mul_mem (H.mul_mem g.property ha) (H.inv_mem g.property)

/-- The next tower subgroup is normalized by the preceding one. -/
theorem conj_mem_next {a g z : G} {H : Subgroup G}
    (hg : g ∈ H) (hz : z ∈ next a H) :
    g*z*g⁻¹ ∈ next a H := by
  change z ∈ Subgroup.closure (conjugatesIn H a) at hz
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k,rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨⟨g*k.val,H.mul_mem hg k.property⟩, ?_⟩
    group
  | one => simpa using (next a H).one_mem
  | mul x y hx hy ihx ihy =>
    have h : g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group
    rw [h]
    exact (next a H).mul_mem ihx ihy
  | inv x hx ih =>
    have h : g*x⁻¹*g⁻¹ = (g*x*g⁻¹)⁻¹ := by group
    rw [h]
    exact (next a H).inv_mem ih

/-- This is the normal-closure commutator step used by the elementary
matrix construction. The convention is xyx⁻¹y⁻¹. -/
theorem comm_mem_next {a g z : G} {H : Subgroup G}
    (hg : g ∈ H) (hz : z ∈ next a H) :
    g*z*g⁻¹*z⁻¹ ∈ next a H :=
  (next a H).mul_mem (conj_mem_next hg hz) ((next a H).inv_mem hz)

/-- The conjugation orbit of a under H, as a subset of the ambient class. -/
def layer (a : G) (H : Subgroup G) : Set (Class a) :=
  {x | ∃ g : H, Class.rho a g.val (Class.anchor a) = x}

theorem layer_top (a : G) : layer a ⊤ = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp x.property
    refine ⟨⟨ConjAct.ofConjAct g,Subgroup.mem_top _⟩, ?_⟩
    apply Subtype.ext
    exact hg

theorem image_layer (a : G) (H : Subgroup G) :
    Subtype.val '' layer a H = conjugatesIn H a := by
  ext y
  constructor
  · rintro ⟨x,⟨g,rfl⟩,rfl⟩
    exact ⟨g,rfl⟩
  · rintro ⟨g,rfl⟩
    exact ⟨Class.rho a g.val (Class.anchor a),⟨g,rfl⟩,rfl⟩

theorem layer_next (a : G) (H : Subgroup G) (ha : a ∈ H) :
    orbitIn (layer a H) (Class.anchor a) = layer a (next a H) := by
  have hgroup : translationGroup (layer a H) =
      (next a H).map (Class.rho a) := by
    rw [Class.translationGroup_eq_map, image_layer]
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp⟩ := MulAction.mem_orbit_iff.mp hx.2
    have hp' := p.property
    rw [hgroup] at hp'
    obtain ⟨g,hg,hgp⟩ := hp'
    refine ⟨⟨g,hg⟩, ?_⟩
    change p.val (Class.anchor a) = x at hp
    rw [hgp]
    exact hp
  · rintro ⟨g,rfl⟩
    refine ⟨⟨⟨g.val,next_le ha g.property⟩,rfl⟩, ?_⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨Class.rho a g.val, ?_⟩,rfl⟩
    rw [hgroup]
    exact ⟨g.val,g.property,rfl⟩

theorem principal_eq_layer (a : G) (n : Nat) :
    principalSeries Set.univ (Class.anchor a) n = layer a (tower a n) := by
  induction n with
  | zero => exact (layer_top a).symm
  | succ n ih =>
    change orbitIn (principalSeries Set.univ (Class.anchor a) n)
      (Class.anchor a) = layer a (next a (tower a n))
    rw [ih, layer_next a (tower a n) (self_mem_tower a n)]

/-- Noncentralizing elements in the tower are precisely the witnesses
needed for the negative first answer. -/
theorem principal_witness_of_tower {a g : G} {n : Nat}
    (hg : g ∈ tower a n) (hne : g*a*g⁻¹ ≠ a) :
    ∃ x y : Class a, y ≠ x ∧ y ∈ principalSeries Set.univ x n := by
  refine ⟨Class.anchor a, Class.rho a g (Class.anchor a), ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · rw [principal_eq_layer]
    exact ⟨⟨g,hg⟩,rfl⟩

end QuandleResearch.Q525
