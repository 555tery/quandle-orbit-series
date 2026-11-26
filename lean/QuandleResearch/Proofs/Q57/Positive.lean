import QuandleResearch.Proofs.Q57.Connected

/-! The first part of BCNW Question 5.7. The proof uses principal
series only as an intermediate device and returns to the original
quantification over every orbit series. -/
namespace QuandleResearch.Q57
open BCNW Issue013
universe u v
variable {X : Type u} {Y : Type v} [_root_.Quandle X] [_root_.Quandle Y]

theorem perm_shelfHom (g : Equiv.Perm X)
    {s : Set X} (hg : g ∈ translationGroup s) :
    ∃ f : ShelfHom X X, ∀ x, f x = g x := by
  refine ⟨{ toFun := g, map_act' := ?_ }, fun _ => rfl⟩
  intro x y
  have he := congrArg (fun p : Equiv.Perm X => p (g y)) (translation_conj hg x)
  change Shelf.act (g x) (g y) = g (Shelf.act x (g.symm (g y))) at he
  rw [Equiv.symm_apply_apply] at he
  exact he.symm

theorem stable_transported {s : Set X} (hs : IsSubrack s)
    {x : X} (hx : x ∈ s) {g : Equiv.Perm X} (hg : g ∈ translationGroup s)
    {n : Nat} (hn : StableAt s x n) :
    StableAt s (g x) n := by
  obtain ⟨f,hf⟩ := perm_shelfHom g hg
  have himage : f '' s = s := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hf]
      exact (translation_preserves hs hg w).mp hw
    · intro hz
      refine ⟨g.symm z, (translation_preserves hs hg (g.symm z)).mpr ?_, ?_⟩
      · simpa only [Equiv.apply_symm_apply] using hz
      · rw [hf,Equiv.apply_symm_apply]
  have he := congrArg (fun t : Set X => f '' t) hn
  change f '' principalSeries s x n = f '' principalSeries s x (n+1) at he
  rw [image_principal f hs hx n, image_principal f hs hx (n+1),himage,hf] at he
  exact he

theorem series_antitone {s : Set X} {a : Nat → Set X} (ha : IsOrbitSeries s a) :
    Antitone a := by
  apply antitone_nat_of_succ_le
  intro n
  obtain ⟨z,hz,he⟩ := ha.2.2 n
  rw [he]
  exact orbitIn_subset _ _

/-- A point in a finite prefix's final term can be used as the
anchor of the entire prefix, without taking an infinite intersection. -/
theorem series_prefix {s : Set X} {a : Nat → Set X}
    (ha : IsOrbitSeries s a) (n : Nat) {y : X} (hy : y ∈ a n) :
    ∀ j ≤ n, principalSeries s y j = a j := by
  intro j
  induction j with
  | zero => intro _; exact ha.1.symm
  | succ j ih =>
    intro hj
    obtain ⟨z,hz,he⟩ := ha.2.2 j
    have hy' : y ∈ a (j+1) := series_antitone ha hj hy
    rw [he] at hy'
    have horb :
        MulAction.orbit (translationGroup (a j)) y =
          MulAction.orbit (translationGroup (a j)) z :=
      MulAction.orbit_eq_iff.mpr hy'.2
    change orbitIn (principalSeries s y j) y = a (j+1)
    rw [ih (Nat.le_trans (Nat.le_succ j) hj), he]
    unfold orbitIn
    rw [horb]

theorem OS_of_principal_stable {s : Set X} (hs : IsSubrack s)
    (h : ∀ x ∈ s, ∃ n, StableAt s x n) : OS s := by
  intro a ha
  obtain ⟨x,hx,he⟩ := ha.2.2 0
  rw [ha.1] at hx
  have hfirst : a 1 = orbitIn s x := by simpa only [ha.1] using he
  obtain ⟨n,hn⟩ := h x hx
  obtain ⟨y,hy,_⟩ := ha.2.2 (n+1)
  have hy1 : y ∈ a 1 := series_antitone ha (by omega) hy
  rw [hfirst] at hy1
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy1.2
  change g.val x = y at hg
  have hny := stable_transported hs hx g.property hn
  rw [hg] at hny
  have hp := series_prefix ha (n+1) hy
  change principalSeries s y n = principalSeries s y (n+1) at hny
  rw [hp n (Nat.le_succ n), hp (n+1) le_rfl] at hny
  exact ⟨n,hny⟩

/-- General-base reduction: restrict to the stabilized image, and
squeeze the fibre series between two tails of the original fibre. -/
theorem additive_stable (f : ShelfHom X Y) (hf : Function.Surjective f)
    (x : X) (r m : Nat)
    (hr : StableAt Set.univ (f x) r)
    (hm : StableAt (fibre f (f x)) x m) :
    StableAt Set.univ x (r+m) := by
  let s : Set X := principalSeries Set.univ x r
  have hs := (principal_mem_and_subrack univ_isSubrack (Set.mem_univ x) r).2
  have hx := (principal_mem_and_subrack univ_isSubrack (Set.mem_univ x) r).1
  have himage : f '' s = principalSeries Set.univ (f x) r := by
    change f '' principalSeries Set.univ x r = _
    rw [image_principal f univ_isSubrack (Set.mem_univ x) r,
      StatementAudit.image_univ_of_surjective f hf]
  have hc : orbitIn (f '' s) (f x) = f '' s := by
    rw [himage]
    exact hr.symm
  have hlo : principalSeries (fibre f (f x)) x r ⊆ s ∩ fibre f (f x) :=
    fun y hy => ⟨principal_mono (Set.subset_univ _) x r hy,
      principal_antitone _ x (Nat.zero_le r) hy⟩
  have hslice : StableAt (s ∩ fibre f (f x)) x m :=
    sandwich_stable hlo Set.inter_subset_right hm
  have h := connected_slice_stable f hs hx hc m hslice
  change principalSeries s x m = principalSeries s x (m+1) at h
  change principalSeries (principalSeries Set.univ x r) x m =
    principalSeries (principalSeries Set.univ x r) x (m+1) at h
  rw [principal_tail,principal_tail] at h
  exact h

theorem extensionOS_proved : extensionOS.{u,v} := by
  intro X Y _ _ _ _ f hf hbase hfibre
  apply OS_of_principal_stable univ_isSubrack
  intro x hx
  obtain ⟨r,hr⟩ := stable_of_OS univ_isSubrack hbase (Set.mem_univ (f x))
  obtain ⟨m,hm⟩ := stable_of_OS (fibre_isSubrack f (f x)) (hfibre (f x))
    (show x ∈ fibre f (f x) from rfl)
  exact ⟨r+m,additive_stable f hf x r m hr hm⟩

#print axioms extensionOS_proved

end QuandleResearch.Q57
