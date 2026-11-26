import QuandleResearch.Proofs.Q57.OrbitTools
import QuandleResearch.Proofs.Q57.Absorption
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! Connected-base step of the 26 November normal-generation proof.
Use the pointwise set action and the stabilizer from Mathlib, rather
than building a separate group of automorphisms of the quotient. -/
namespace QuandleResearch.Q57
open BCNW Issue013
open scoped Pointwise
variable {X Y : Type*} [_root_.Quandle X] [_root_.Quandle Y]

theorem translation_respects_fibre (f : ShelfHom X Y)
    {s : Set X} {g : Equiv.Perm X} (hg : g ∈ translationGroup s) :
    ∀ y z : X, f y = f z ↔ f (g y) = f (g z) := by
  change g ∈ Subgroup.closure ((_root_.Rack.act' : X → Equiv.Perm X) '' s) at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨w, hw, rfl⟩ := hg
    intro y z
    simp only [Rack.act'_apply, f.map_act]
    exact ⟨fun h => congrArg (Shelf.act (f w)) h,
      (_root_.Rack.act' (f w)).injective⟩
  | one => intro y z; rfl
  | mul g h hg hh ig ih =>
    intro y z
    exact (ih y z).trans (ig (h y) (h z))
  | inv g hg ih =>
    intro y z
    change f y = f z ↔ f (g.symm y) = f (g.symm z)
    simpa only [Equiv.apply_symm_apply] using (ih (g.symm y) (g.symm z)).symm

theorem mem_set_stabilizer_iff (s : Set X) (g : Equiv.Perm X) :
    g ∈ MulAction.stabilizer (Equiv.Perm X) s ↔
      ∀ z : X, z ∈ s ↔ g z ∈ s := by
  change g '' s = s ↔ _
  constructor
  · intro h z
    constructor
    · intro hz
      have hz' : g z ∈ g '' s := ⟨z,hz,rfl⟩
      rwa [h] at hz'
    · intro hz
      rw [← h] at hz
      obtain ⟨w,hw,he⟩ := hz
      exact (g.injective he) ▸ hw
  · intro h
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (h w).mp hw
    · intro hz
      refine ⟨g.symm z, (h (g.symm z)).mpr ?_, g.apply_symm_apply z⟩
      simpa only [Equiv.apply_symm_apply] using hz

theorem translation_sends_into (s : Set X) (hs : IsSubrack s)
    (x : X) (hx : x ∈ s) {g : Equiv.Perm X} (hg : g ∈ translationGroup s) :
    g x ∈ orbitIn s x :=
  ⟨(translation_preserves hs hg x).mp hx,
    MulAction.mem_orbit_iff.mpr ⟨⟨g,hg⟩,rfl⟩⟩

theorem slice_subrack (f : ShelfHom X Y) {s : Set X} (hs : IsSubrack s)
    (b : Y) : IsSubrack (s ∩ fibre f b) := by
  intro y hy x hx
  exact ⟨⟨(hs y hy.1 x hx.1).1,(fibre_isSubrack f b y hy.2 x hx.2).1⟩,
    ⟨(hs y hy.1 x hx.1).2,(fibre_isSubrack f b y hy.2 x hx.2).2⟩⟩

/-- Group-orbit saturation, written as native permutation witnesses. -/
def Saturates (G : Subgroup (Equiv.Perm X)) (F P : Set X) : Prop :=
  ∀ y ∈ P, ∃ g ∈ G, ∃ z ∈ F, g z = y

/-- Connected image, with a chosen anchor, suffices for the fibre
stabilization bound. This version works on ambient subquandles. -/
theorem connected_slice_stable (f : ShelfHom X Y)
    {s : Set X} (hs : IsSubrack s) {x : X} (hx : x ∈ s)
    (hc : orbitIn (f '' s) (f x) = f '' s)
    (m : Nat) (hm : StableAt (s ∩ fibre f (f x)) x m) :
    StableAt s x m := by
  let F : Set X := s ∩ fibre f (f x)
  let P : Nat → Set X := principalSeries s x
  let E : Nat → Set X := principalSeries F x
  let G : Nat → Subgroup (Equiv.Perm X) := fun i => translationGroup (P i)
  let U : Nat → Subgroup (Equiv.Perm X) := fun i => translationGroup (E i)
  let K : Subgroup (Equiv.Perm X) :=
    translationGroup s ⊓ MulAction.stabilizer (Equiv.Perm X) F
  have hF : IsSubrack F := slice_subrack f hs (f x)
  have hxF : x ∈ F := ⟨hx,rfl⟩
  have hP (i : Nat) := principal_mem_and_subrack hs hx i
  have hE (i : Nat) := principal_mem_and_subrack hF hxF i
  have hEP (i : Nat) : E i ⊆ P i := principal_mono Set.inter_subset_left x i
  have hUG (i : Nat) : U i ≤ G i := translationGroup_mono (hEP i)
  have hGG (i : Nat) : G (i+1) ≤ G i := translationGroup_mono (orbitIn_subset _ _)
  have hUU (i : Nat) : U (i+1) ≤ U i := translationGroup_mono (orbitIn_subset _ _)
  have hG0 (i : Nat) : G i ≤ translationGroup s :=
    translationGroup_mono (principal_antitone s x (Nat.zero_le i))
  have hU0 (i : Nat) : U i ≤ U 0 :=
    translationGroup_mono (principal_antitone F x (Nat.zero_le i))
  have hgn (i : Nat) : G i ≤ Subgroup.normalizer (G (i+1)) :=
    orbit_step_normalizer (hP i).2 x
  have hun (i : Nat) : U i ≤ Subgroup.normalizer (U (i+1)) :=
    orbit_step_normalizer (hE i).2 x
  have hKU : K ≤ Subgroup.normalizer (U 0) := by
    apply normalizer_of_preserves (t := s) inf_le_left
    intro g hg y hy
    exact ((mem_set_stabilizer_iff F g).mp hg.2 y).mp hy
  have hUK : U 0 ≤ K := by
    apply le_inf ((hUG 0).trans (hG0 0)) ?_
    intro g hg
    exact (mem_set_stabilizer_iff F g).mpr (translation_preserves hF hg)
  have himage : ∀ i, f '' P i = f '' s := by
    intro i
    rw [image_principal f hs hx i]
    induction i with
    | zero => rfl
    | succ i ih =>
      change orbitIn (principalSeries (f '' s) (f x) i) (f x) = f '' s
      rw [ih,hc]
  have hcomp (i : Nat) : G (i+1) ⊔ (K ⊓ G i) = G i := by
    apply le_antisymm (sup_le (hGG i) inf_le_right)
    intro g hg
    have hgi := translation_sends_into (P i) (hP i).2 x (hP i).1 hg
    have hfg : f (g x) ∈ f '' P (i+2) := by
      rw [himage (i+2), ← himage (i+1)]
      exact ⟨g x,hgi,rfl⟩
    obtain ⟨w,hw,he⟩ := hfg
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hw.2
    change h.val x = w at hh
    let k : Equiv.Perm X := h.val⁻¹ * g
    have hhG : h.val ∈ G i := hGG i h.property
    have hkG : k ∈ G i := (G i).mul_mem ((G i).inv_mem hhG) hg
    have hk0 : k ∈ translationGroup s := hG0 i hkG
    have hfix : f (k x) = f x := by
      apply (translation_respects_fibre f (hG0 (i+1) h.property) (k x) x).mpr
      change f (h.val (h.val.symm (g x))) = f (h.val x)
      rw [Equiv.apply_symm_apply,hh,he]
    have hkK : k ∈ K := by
      refine ⟨hk0,(mem_set_stabilizer_iff F k).mpr ?_⟩
      intro z
      change (z ∈ s ∧ f z = f x) ↔ (k z ∈ s ∧ f (k z) = f x)
      exact and_congr (translation_preserves hs hk0 z)
        ((translation_respects_fibre f hk0 z x).trans
          (by rw [hfix]))
    have hprod : h.val * k = g := by dsimp [k]; group
    rw [← hprod]
    exact Subgroup.mul_mem _ (le_sup_left h.property) (le_sup_right ⟨hkK,hkG⟩)
  have hsat : ∀ i, Saturates (G i) (E i) (P i) := by
    intro i
    induction i with
    | zero =>
      intro y hy
      have hfy : f y ∈ f '' P 1 := by rw [himage 1]; exact ⟨y,hy,rfl⟩
      obtain ⟨w,hw,he⟩ := hfy
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hw.2
      change g.val x = w at hg
      let z := g.val.symm y
      have hz : z ∈ F := by
        have hzS : z ∈ s := (translation_preserves hs g.property z).mpr
          (by simpa [z] using hy)
        have hzB : f z = f x := by
          apply (translation_respects_fibre f g.property z x).mpr
          simpa [z,hg,he]
        exact ⟨hzS,hzB⟩
      exact ⟨g.val,g.property,z,hz,g.val.apply_symm_apply y⟩
    | succ i ih =>
      let V : Nat → Subgroup (Equiv.Perm X)
        | 0 => K ⊓ G i
        | j+1 => U j ⊓ G i
      have hV (j : Nat) : V j ≤ G i := by cases j <;> exact inf_le_right
      have hstep (j : Nat) : V j ≤ Subgroup.normalizer (V (j+1)) := by
        cases j with
        | zero =>
          exact (le_inf (inf_le_left.trans hKU)
            (inf_le_right.trans (G i).le_normalizer)).trans
              Subgroup.inf_normalizer_le_normalizer_inf
        | succ j =>
          exact (le_inf (inf_le_left.trans (hun j))
            (inf_le_right.trans (G i).le_normalizer)).trans
              Subgroup.inf_normalizer_le_normalizer_inf
      have hgen (W : Subgroup (Equiv.Perm X)) (hW : W ≤ G i)
          (hn : G i ≤ Subgroup.normalizer W) (hu : U i ≤ W) : G i ≤ W := by
        apply Subgroup.closure_le.mpr
        rintro _ ⟨y,hy,rfl⟩
        obtain ⟨g,hg,z,hz,rfl⟩ := ih y hy
        rw [translation_conj hg z]
        exact (Subgroup.le_normalizer_iff.mp hn) g hg _ (hu (translation_mem hz))
      have hUiV : ∀ j ≤ i+1, U i ≤ V j := by
        intro j hj
        cases j with
        | zero => exact le_inf ((hU0 i).trans hUK) (hUG i)
        | succ j =>
          exact le_inf (translationGroup_mono
            (principal_antitone F x (Nat.le_of_succ_le_succ hj))) (hUG i)
      have hab := absorb_normal_chain (G i) (G (i+1)) (U i) V
        (hGG i) (hgn i) hV hstep (hcomp i) hgen (i+1) hUiV
      have hjoin : G (i+1) ⊔ U i = G i := by
        change G (i+1) ⊔ (U i ⊓ G i) = G i at hab
        simpa only [inf_of_le_left (hUG i)] using hab
      intro y hy
      obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy.2
      change g.val x = y at hg
      obtain ⟨h,hh,u,hu,he⟩ := factor_of_join (hgn i) (hUG i) hjoin g.property
      refine ⟨h,hh,u x,translation_sends_into (E i) (hE i).2 x (hE i).1 hu,?_⟩
      change (h*u) x = y
      rw [he,hg]
  change P m = P (m+1)
  apply Set.Subset.antisymm ?_ (orbitIn_subset _ _)
  intro y hy
  obtain ⟨g,hg,z,hz,rfl⟩ := hsat m y hy
  have hm' : E m = E (m+1) := hm
  rw [hm'] at hz
  obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp hz.2
  change u.val x = z at hu
  rw [← hu]
  have hgu : g*u.val ∈ G m := (G m).mul_mem hg (hUG m u.property)
  exact translation_sends_into (P m) (hP m).2 x (hP m).1 hgu

end QuandleResearch.Q57
