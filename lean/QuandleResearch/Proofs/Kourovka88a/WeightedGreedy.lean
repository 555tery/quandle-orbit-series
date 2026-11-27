import QuandleResearch.Proofs.Kourovka88a.Heights

/-!
# Weighted greedy stages

This is the algebraic construction with a genuine minimal-weight
choice, rather than a presumed enumeration in weight order. We prove
coverage by counting the finitely many remaining bad words in a fixed
ball. Ties between words of the same weight are unrestricted here.
Guba's additional precedence constraints and geometric survival must
still be established separately.

The choice of conjugator is allowed to depend on the rank, the previous
normal subgroup, and the chosen bad word.
-/

namespace QuandleResearch.Issue070

def MinBad (N : Subgroup F) (c : F) : Prop :=
  ¬ Good N c ∧ ∀ w : F, ¬ Good N w → weightedLength c ≤ weightedLength w

theorem exists_minBad (N : Subgroup F) (h : ∃ w : F, ¬ Good N w) :
    ∃ c : F, MinBad N c := by
  classical
  obtain ⟨w, hw⟩ := h
  have hex : ∃ n : ℕ, ∃ c : F, ¬ Good N c ∧ weightedLength c = n :=
    ⟨weightedLength w, w, hw, rfl⟩
  obtain ⟨c, hc, hlen⟩ := Nat.find_spec hex
  refine ⟨c, hc, ?_⟩
  intro v hv
  rw [hlen]
  exact Nat.find_min' hex ⟨v, hv, rfl⟩

noncomputable def badBall (N : Subgroup F) (d : ℕ) : Finset F := by
  classical
  exact (weightedBallCover d).toFinset.filter
    (fun w => weightedLength w ≤ d ∧ ¬ Good N w)

theorem mem_badBall (N : Subgroup F) (d : ℕ) (w : F) :
    w ∈ badBall N d ↔ weightedLength w ≤ d ∧ ¬ Good N w := by
  classical
  unfold badBall
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨List.mem_toFinset.mpr (mem_weightedBallCover d w h.1), h⟩

theorem badBall_subset {N M : Subgroup F} (hNM : N ≤ M) (d : ℕ) :
    badBall M d ⊆ badBall N d := by
  intro w hw
  obtain ⟨hlen, hbad⟩ := (mem_badBall M d w).mp hw
  exact (mem_badBall N d w).mpr ⟨hlen, fun hg => hbad (good_mono hNM hg)⟩

/-- Progress is measured by the number of bad words of bounded weight.
The estimate holds for any minimal-weight tie selection. -/
theorem badBall_card_decreases {N M : Subgroup F} (hNM : N ≤ M)
    (d : ℕ) {c : F} (hc : ¬ Good N c)
    (hlen : weightedLength c ≤ d) (hg : Good M c) :
    (badBall M d).card < (badBall N d).card := by
  have hmem : c ∈ badBall N d := (mem_badBall N d c).mpr ⟨hlen, hc⟩
  have hnmem : c ∉ badBall M d := fun hm => ((mem_badBall M d c).mp hm).2 hg
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨badBall_subset hNM d, ?_⟩
  intro heq
  exact hnmem (heq.symm ▸ hmem)

/-- No global enumeration or decidability of Good is needed.
A word which never became good would force infinitely many strict
decreases of the cardinality of its own finite bad ball. -/
theorem weighted_cover (N : ℕ → Subgroup F) (hN : Monotone N)
    (hstep : ∀ i w, ¬ Good (N i) w →
      ∃ c, MinBad (N i) c ∧ Good (N (i+1)) c) :
    ∀ w : F, ∃ i, Good (N i) w := by
  intro w
  by_contra h
  have hbad : ∀ i, ¬ Good (N i) w := fun i hi => h ⟨i, hi⟩
  let d := weightedLength w
  have hdesc : ∀ i, (badBall (N (i+1)) d).card < (badBall (N i) d).card := by
    intro i
    obtain ⟨c, hc, hg⟩ := hstep i w (hbad i)
    exact badBall_card_decreases (hN (Nat.le_succ i)) d hc.1
      (hc.2 w (hbad i)) hg
  have hbound : ∀ i, (badBall (N i) d).card + i ≤ (badBall (N 0) d).card := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hd := hdesc i
      omega
  have himpossible := hbound ((badBall (N 0) d).card + 1)
  omega

/-- A selector may be supplied to accommodate the published tie order.
The default classical choice below proves that the interface is inhabited,
not that its default tie selection is Guba-admissible. -/
def WeightedSelector :=
  ∀ N : Subgroup F, (∃ w : F, ¬ Good N w) → {c : F // MinBad N c}

noncomputable def arbitraryWeightedSelector : WeightedSelector :=
  fun N h => ⟨Classical.choose (exists_minBad N h),
    Classical.choose_spec (exists_minBad N h)⟩

abbrev ConjugatorChoice := ℕ → Subgroup F → F → F

noncomputable def weightedRelator (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) (N : Subgroup F) : F := by
  classical
  exact if h : ∃ w : F, ¬ Good N w then
    let c := (pick N h).val
    heightRelator (X i N c) c 1
  else 1

theorem weightedRelator_eq (pick : WeightedSelector) (X : ConjugatorChoice)
    (i : ℕ) (N : Subgroup F) (h : ∃ w : F, ¬ Good N w) :
    weightedRelator pick X i N =
      heightRelator (X i N (pick N h).val) (pick N h).val 1 := by
  classical
  simp only [weightedRelator, dite_eq_left h]

noncomputable def weightedStages (pick : WeightedSelector)
    (X : ConjugatorChoice) : ℕ → Subgroup F
  | 0 => ⊥
  | i+1 => adjoin (weightedStages pick X i)
      (weightedRelator pick X i (weightedStages pick X i))

theorem weightedStages_normal (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) : (weightedStages pick X i).Normal := by
  cases i with
  | zero =>
    change (⊥ : Subgroup F).Normal
    infer_instance
  | succ i =>
    change (adjoin _ _).Normal
    infer_instance

theorem weightedStages_mono (pick : WeightedSelector) (X : ConjugatorChoice) :
    Monotone (weightedStages pick X) := by
  apply monotone_nat_of_le_succ
  intro i
  exact le_adjoin _ _

theorem weightedStages_progress (pick : WeightedSelector) (X : ConjugatorChoice)
    (i : ℕ) (w : F) (hw : ¬ Good (weightedStages pick X i) w) :
    ∃ c, MinBad (weightedStages pick X i) c ∧
      Good (weightedStages pick X (i+1)) c := by
  let N := weightedStages pick X i
  have h : ∃ v : F, ¬ Good N v := ⟨w, hw⟩
  let c := (pick N h).val
  refine ⟨c, (pick N h).property, X i N c, 1, ?_⟩
  rw [zpow_one]
  change heightRelator (X i N c) c 1 ∈ adjoin N (weightedRelator pick X i N)
  rw [← weightedRelator_eq pick X i N h]
  exact relator_mem_adjoin _ _

theorem weightedStages_cover (pick : WeightedSelector) (X : ConjugatorChoice) :
    ∀ w : F, ∃ i, Good (weightedStages pick X i) w :=
  weighted_cover _ (weightedStages_mono pick X) (weightedStages_progress pick X)

/-- This construction no longer requires an enumeration as a hypothesis.
Survival of the commutator for a suitable selector and conjugator choice
remains the missing mathematical input. -/
theorem answer_of_weightedStages (pick : WeightedSelector) (X : ConjugatorChoice)
    (hsurvive : ∀ i, commWord ∉ weightedStages pick X i) : answer :=
  answer_of_chain _ (weightedStages_mono pick X) (weightedStages_normal pick X)
    hsurvive (weightedStages_cover pick X)

theorem answer_of_weightedStages_short (pick : WeightedSelector) (X : ConjugatorChoice)
    (hshort : ∀ i w, w ∈ weightedStages pick X i →
      weightedLength w ≤ 2 + 2 * 10 ^ 80 → w = 1) : answer := by
  apply answer_of_weightedStages pick X
  intro i hi
  exact commWord_ne_one (hshort i commWord hi (le_of_eq weightedLength_commWord))

end QuandleResearch.Issue070
