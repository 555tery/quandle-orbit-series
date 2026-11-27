import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Kourovka Notebook 8.8(a): the algebraic part of Guba's construction

Source: V. S. Guba, *A finitely generated complete group*,
Math. USSR-Izv. 29 (1987), Theorem 2, DOI 10.1070/IM1987V029N02ABEH000969.
Issue #70: https://github.com/555tery/quandle-orbit-series/issues/70

This module proves conditional reductions only. It does not assert the
existence of Guba's sequence with a surviving commutator, nor does it
formalize the geometric estimates in Lemma 23 of that paper.
-/

namespace QuandleResearch.Issue070

/-- Exact universe-zero target of Formal Conjectures' Kourovka 8.8(a). -/
def answer : Prop :=
  ∃ (G : Type) (_ : Group G), ¬ IsCyclic G ∧ Group.FG G ∧
    ∃ a : G, ∀ g : G, ∃ n : ℤ, IsConj g (a ^ n)

abbrev F := FreeGroup (Fin 2)

def a : F := FreeGroup.of 0
def b : F := FreeGroup.of 1
def commWord : F := a * b * a⁻¹ * b⁻¹

/-- A word is good if its image is conjugate to a power of a.
The conjugator is represented by a word in the free group. -/
def Good (N : Subgroup F) (w : F) : Prop :=
  ∃ (x : F) (k : ℤ), x * w * x⁻¹ * (a ^ k)⁻¹ ∈ N

theorem good_mono {N M : Subgroup F} (hNM : N ≤ M) {w : F}
    (hw : Good N w) : Good M w := by
  obtain ⟨x, k, hx⟩ := hw
  exact ⟨x, k, hNM hx⟩

/-- A relation in the normal subgroup is exactly conjugacy in the quotient. -/
theorem good_iff_quotient (N : Subgroup F) [N.Normal] (w : F) :
    Good N w ↔ ∃ k : ℤ,
      IsConj (QuotientGroup.mk' N w) ((QuotientGroup.mk' N a) ^ k) := by
  constructor
  · rintro ⟨x, k, hx⟩
    refine ⟨k, isConj_iff.mpr ⟨QuotientGroup.mk' N x, ?_⟩⟩
    have hr : QuotientGroup.mk' N (x * w * x⁻¹ * (a ^ k)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    have hr' : QuotientGroup.mk' N x * QuotientGroup.mk' N w *
        (QuotientGroup.mk' N x)⁻¹ *
        ((QuotientGroup.mk' N a) ^ k)⁻¹ = 1 := by
      simpa only [map_mul, map_inv, map_zpow] using hr
    calc
      _ = (QuotientGroup.mk' N x * QuotientGroup.mk' N w *
          (QuotientGroup.mk' N x)⁻¹ *
          ((QuotientGroup.mk' N a) ^ k)⁻¹) *
          ((QuotientGroup.mk' N a) ^ k) := by group
      _ = _ := by rw [hr', one_mul]
  · rintro ⟨k, hk⟩
    obtain ⟨q, hq⟩ := isConj_iff.mp hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨x, k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    change QuotientGroup.mk' N (x * w * x⁻¹ * (a ^ k)⁻¹) = 1
    simp only [map_mul, map_inv, map_zpow]
    rw [hq, mul_inv_cancel]

/-- Union of an increasing sequence, expressed as a Mathlib supremum. -/
theorem mem_limit_iff (N : ℕ → Subgroup F) (hN : Monotone N) (w : F) :
    w ∈ (⨆ n, N n) ↔ ∃ n, w ∈ N n := by
  apply Subgroup.mem_iSup_of_directed
  intro i j
  exact ⟨max i j, hN (le_max_left i j), hN (le_max_right i j)⟩

theorem limit_normal (N : ℕ → Subgroup F) (hN : Monotone N)
    (hn : ∀ n, (N n).Normal) : (⨆ n, N n).Normal := by
  constructor
  intro x hx g
  obtain ⟨i, hi⟩ := (mem_limit_iff N hN x).mp hx
  exact (mem_limit_iff N hN _).mpr ⟨i, (hn i).conj_mem x hi g⟩

/-- The exact algebraic reduction: the only noncollapse assumption is
survival of a fixed free-group commutator at every finite stage. -/
theorem answer_of_chain (N : ℕ → Subgroup F) (hN : Monotone N)
    (hn : ∀ n, (N n).Normal)
    (hsurvive : ∀ n, commWord ∉ N n)
    (hcover : ∀ w : F, ∃ n, Good (N n) w) : answer := by
  let L : Subgroup F := ⨆ n, N n
  letI : L.Normal := limit_normal N hN hn
  let q := QuotientGroup.mk' L
  have hcomm : q commWord ≠ 1 := by
    intro he
    have hm : commWord ∈ L := (QuotientGroup.eq_one_iff _).mp he
    obtain ⟨i, hi⟩ := (mem_limit_iff N hN commWord).mp hm
    exact hsurvive i hi
  refine ⟨F ⧸ L, inferInstance, ?_, inferInstance, q a, ?_⟩
  · intro hc
    letI : IsCyclic (F ⧸ L) := hc
    letI : CommGroup (F ⧸ L) := IsCyclic.commGroup
    apply hcomm
    change q (a * b * a⁻¹ * b⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_comm (q a) (q b)]
    group
  · intro g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective L g
    obtain ⟨i, hi⟩ := hcover w
    exact (good_iff_quotient L w).mp (good_mono (le_iSup N i) hi)

/-- Prefix normal closure: stage n contains precisely the first n relators
as normal generators. In particular stage zero has no relators. -/
def stage (R : ℕ → F) (n : ℕ) : Subgroup F :=
  Subgroup.normalClosure {w | ∃ j < n, R j = w}

instance stageNormal (R : ℕ → F) (n : ℕ) : (stage R n).Normal := by
  unfold stage
  infer_instance

theorem stage_mono (R : ℕ → F) : Monotone (stage R) := by
  intro i j hij
  apply Subgroup.normalClosure_mono
  rintro w ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

theorem relator_mem_next_stage (R : ℕ → F) (i : ℕ) :
    R i ∈ stage R (i + 1) :=
  Subgroup.subset_normalClosure ⟨i, Nat.lt_succ_self i, rfl⟩

/-- Greedy progress does not require deciding whether a word is good.
The least bad word becomes good at the next stage; if none exists,
all words are already good. The enumeration can repeat elements. -/
theorem greedy_cover (N : ℕ → Subgroup F) (hN : Monotone N)
    (words : ℕ → F) (hwords : Function.Surjective words)
    (hgreedy : ∀ i j, ¬ Good (N i) (words j) →
      (∀ k < j, Good (N i) (words k)) → Good (N (i + 1)) (words j)) :
    ∀ w : F, ∃ i, Good (N i) w := by
  have hall : ∀ n j, j < n → Good (N n) (words j) := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      intro j hj
      by_cases hlt : j < n
      · exact good_mono (hN (Nat.le_succ n)) (ih j hlt)
      · have heq : j = n := by omega
        subst j
        by_cases hg : Good (N n) (words n)
        · exact good_mono (hN (Nat.le_succ n)) hg
        · exact hgreedy n n hg ih
  intro w
  obtain ⟨j, rfl⟩ := hwords w
  exact ⟨j + 1, hall (j + 1) j (Nat.lt_succ_self j)⟩

/-- Algebraic Guba-style reduction. The geometric survival input is
an explicit hypothesis, not an axiom or a proved fact in this module.
The relation choice is abstract; Guba's concrete weighted ordering and
long conjugating words still have to be constructed and verified. -/
theorem answer_of_greedy_relators (R words : ℕ → F)
    (hwords : Function.Surjective words)
    (hsurvive : ∀ n, commWord ∉ stage R n)
    (hchoice : ∀ i j, ¬ Good (stage R i) (words j) →
      (∀ k < j, Good (stage R i) (words k)) →
      ∃ (x : F) (m : ℤ), R i = x * words j * x⁻¹ * (a ^ m)⁻¹) :
    answer := by
  apply answer_of_chain (stage R) (stage_mono R) (fun n => stageNormal R n) hsurvive
  apply greedy_cover (stage R) (stage_mono R) words hwords
  intro i j hbad hprev
  obtain ⟨x, m, hr⟩ := hchoice i j hbad hprev
  refine ⟨x, m, ?_⟩
  rw [← hr]
  exact relator_mem_next_stage R i

end QuandleResearch.Issue070
