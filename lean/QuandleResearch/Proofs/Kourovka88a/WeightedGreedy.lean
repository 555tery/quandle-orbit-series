import QuandleResearch.Proofs.Kourovka88a.Heights
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

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
  rw [zpow_one, ← heightRelator_one (X i N c) c]
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


/-- The actual rank-indexed relators, extracted from the recursive stages. -/
noncomputable def weightedRankRelator (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) : F :=
  weightedRelator pick X i (weightedStages pick X i)

/-- A recursive stage is exactly the normal closure of its preceding
height-one rank relators. No geometric or survival assumptions are used. -/
theorem weightedStages_eq_stage (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) :
    weightedStages pick X n = stage (weightedRankRelator pick X) n := by
  induction n with
  | zero =>
    change (⊥ : Subgroup F) =
      Subgroup.normalClosure {w | ∃ j < 0, weightedRankRelator pick X j = w}
    apply le_antisymm bot_le
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨j, hj, _⟩
    omega
  | succ n ih =>
    change adjoin (weightedStages pick X n) (weightedRankRelator pick X n) =
      stage (weightedRankRelator pick X) (n+1)
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      intro w hw
      rcases hw with hw | hw
      · have hm : w ∈ weightedStages pick X n := hw
        rw [ih] at hm
        exact stage_mono _ (Nat.le_succ n) hm
      · have heq : w = weightedRankRelator pick X n := hw
        subst w
        exact relator_mem_next_stage _ n
    · apply Subgroup.normalClosure_le_normal
      rintro w ⟨j, hj, rfl⟩
      by_cases h : j < n
      · apply (le_adjoin (weightedStages pick X n) (weightedRankRelator pick X n))
        rw [ih]
        exact Subgroup.subset_normalClosure ⟨j, h, rfl⟩
      · have heq : j = n := by omega
        subst j
        exact relator_mem_adjoin _ _

/-- All integer-height relators at an actual rank. A stationary rank
contributes only the identity at every height. -/
noncomputable def weightedRankHeightRelator (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) (k : ℤ) : F := by
  classical
  let N := weightedStages pick X i
  exact if h : ∃ w : F, ¬ Good N w then
    let c := (pick N h).val
    heightRelator (X i N c) c k
  else 1

theorem weightedRankHeightRelator_one (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) :
    weightedRankHeightRelator pick X i 1 = weightedRankRelator pick X i := by
  rfl

/-- In any normal subgroup, membership at height one implies membership
at every integer height for the same actual rank. -/
theorem weightedRankHeightRelator_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) (M : Subgroup F) [M.Normal]
    (h1 : weightedRankRelator pick X i ∈ M) (k : ℤ) :
    weightedRankHeightRelator pick X i k ∈ M := by
  classical
  by_cases h : ∃ w : F, ¬ Good (weightedStages pick X i) w
  · rw [weightedRankRelator, weightedRelator_eq pick X i _ h] at h1
    have hk := heightRelator_mem_of_one M
      (X i (weightedStages pick X i) (pick (weightedStages pick X i) h).val)
      (pick (weightedStages pick X i) h).val h1 k
    simpa only [weightedRankHeightRelator, dite_eq_left h] using hk
  · have heq : weightedRankHeightRelator pick X i k = 1 := by
      simp only [weightedRankHeightRelator, dite_eq_right h]
    rw [heq]
    exact Subgroup.one_mem M

/-- Presentation using all ranks below n and all integral heights. This
is the algebraic presentation needed by the graded-diagram argument. -/
def weightedHeightStage (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) : Subgroup F :=
  Subgroup.normalClosure
    {w | ∃ i < n, ∃ k : ℤ, weightedRankHeightRelator pick X i k = w}

/-- Exact equality of the all-height presentation and the recursively
defined stage, not merely an equality of their quotient cardinalities. -/
theorem weightedHeightStage_eq (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) :
    weightedHeightStage pick X n = weightedStages pick X n := by
  rw [weightedStages_eq_stage]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro w ⟨i, hi, k, rfl⟩
    apply weightedRankHeightRelator_mem
    exact Subgroup.subset_normalClosure ⟨i, hi, rfl⟩
  · unfold stage weightedHeightStage
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨i, hi, rfl⟩
    apply Subgroup.subset_normalClosure
    exact ⟨i, hi, 1, weightedRankHeightRelator_one pick X i⟩

/-- The remaining diagram input can now refer directly to the
all-height presentation, rather than to the implementation of recursion.
This is still a conditional reduction, not a proof of survival. -/
theorem answer_of_heightStages_short (pick : WeightedSelector)
    (X : ConjugatorChoice)
    (hshort : ∀ i w, w ∈ weightedHeightStage pick X i →
      weightedLength w ≤ 2 + 2 * 10 ^ 80 → w = 1) : answer := by
  apply answer_of_weightedStages_short pick X
  intro i w hw hlen
  apply hshort i w _ hlen
  rw [weightedHeightStage_eq]
  exact hw


/-- The merger identity holds for the actual rank-indexed relation family,
including the inactive-rank case. No assertion about adjacency is made. -/
theorem weightedRankHeightRelator_add (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) (k l : ℤ) :
    weightedRankHeightRelator pick X i (k+l) =
      weightedRankHeightRelator pick X i k * a^k *
        weightedRankHeightRelator pick X i l * (a^k)⁻¹ := by
  classical
  by_cases h : ∃ w : F, ¬ Good (weightedStages pick X i) w
  · simp only [weightedRankHeightRelator, dite_eq_left h]
    exact heightRelator_add _ _ k l
  · simp [weightedRankHeightRelator, h]

theorem weightedRankHeightRelator_zero (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ) :
    weightedRankHeightRelator pick X i 0 = 1 := by
  classical
  by_cases h : ∃ w : F, ¬ Good (weightedStages pick X i) w
  · simp only [weightedRankHeightRelator, dite_eq_left h, heightRelator_zero]
  · simp [weightedRankHeightRelator, h]


/-! ## Minimal periods

The weight-minimal choice implies cyclic reduction and minimality in
the preceding quotient, without assuming geometric survival.
Use Mathlib's literal cyclic-reduction decomposition, rather than
reimplementing cancellation at the ends of a free word.
-/

theorem good_conjugate_iff (N : Subgroup F) (u w : F) :
    Good N (u*w*u⁻¹) ↔ Good N w := by
  constructor
  · rintro ⟨x,k,hx⟩
    refine ⟨x*u,k,?_⟩
    have he : (x*u)*w*(x*u)⁻¹*(a^k)⁻¹ = x*(u*w*u⁻¹)*x⁻¹*(a^k)⁻¹ := by group
    rw [he]
    exact hx
  · rintro ⟨x,k,hx⟩
    refine ⟨x*u⁻¹,k,?_⟩
    have he : (x*u⁻¹)*(u*w*u⁻¹)*(x*u⁻¹)⁻¹*(a^k)⁻¹ = x*w*x⁻¹*(a^k)⁻¹ := by group
    rw [he]
    exact hx

theorem minBad_shorter_good {N : Subgroup F} {c : F}
    (hc : MinBad N c) {w : F} (hw : weightedLength w < weightedLength c) :
    Good N w := by
  by_contra h
  exact (not_lt_of_ge (hc.2 w h)) hw

theorem minBad_cyclicallyReduced {N : Subgroup F} {c : F}
    (hc : MinBad N c) : FreeGroup.IsCyclicallyReduced c.toWord := by
  let u := FreeGroup.reduceCyclically.conjugator c.toWord
  let v := FreeGroup.reduceCyclically c.toWord
  have hword : u ++ v ++ FreeGroup.invRev u = c.toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically _
  have hgroup : FreeGroup.mk u * FreeGroup.mk v * (FreeGroup.mk u)⁻¹ = c := by
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk, hword, FreeGroup.mk_toWord]
  have hbad : ¬ Good N (FreeGroup.mk v) := by
    intro hv
    apply hc.1
    rw [← hgroup]
    exact (good_conjugate_iff N _ _).mpr hv
  have hmin := hc.2 _ hbad
  have hle := weightedLength_mk_le v
  have heq : weightedLength c = rawWeight u + rawWeight v + rawWeight (FreeGroup.invRev u) := by
    unfold weightedLength
    rw [← hword, rawWeight_append, rawWeight_append]
  have hu : rawWeight u = 0 := by omega
  have hunil := (rawWeight_eq_zero_iff u).mp hu
  have hv : v = c.toWord := by
    simpa [hunil] using hword
  rw [← hv]
  exact FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord

/-- No shorter representative of the same element of the preceding
quotient can be a minimal bad period. -/
theorem minBad_quotient_length {N : Subgroup F} [N.Normal] {c w : F}
    (hc : MinBad N c)
    (heq : QuotientGroup.mk' N c = QuotientGroup.mk' N w) :
    weightedLength c ≤ weightedLength w := by
  apply hc.2
  intro hw
  apply hc.1
  apply (good_iff_quotient N c).mpr
  rw [heq]
  exact (good_iff_quotient N w).mp hw

/-- Each strictly shorter literal factor of a minimal period is good.
No assumption on the reduction of the factor is required. -/
theorem minBad_proper_factor_good {N : Subgroup F} {c : F}
    (hc : MinBad N c) (p v r : RawWord)
    (heq : c.toWord = p ++ v ++ r) (hproper : p ≠ [] ∨ r ≠ []) :
    Good N (FreeGroup.mk v) := by
  apply minBad_shorter_good hc
  have hle := weightedLength_mk_le v
  have hweight : weightedLength c = rawWeight p + rawWeight v + rawWeight r := by
    unfold weightedLength
    rw [heq, rawWeight_append, rawWeight_append]
  rcases hproper with hp | hr
  · have hpos : 0 < rawWeight p := by
      by_contra! hn
      exact hp ((rawWeight_eq_zero_iff p).mp (by omega))
    omega
  · have hpos : 0 < rawWeight r := by
      by_contra! hn
      exact hr ((rawWeight_eq_zero_iff r).mp (by omega))
    omega


/-- Goodness is closed under taking natural powers in the quotient. -/
theorem good_pow (N : Subgroup F) [N.Normal] {w : F}
    (hw : Good N w) (m : ℕ) : Good N (w^m) := by
  obtain ⟨k,hk⟩ := (good_iff_quotient N w).mp hw
  apply (good_iff_quotient N (w^m)).mpr
  refine ⟨k*(m:ℤ), ?_⟩
  rw [map_pow, zpow_mul, zpow_natCast]
  exact IsConj.pow m hk

theorem rawWeight_rawNatPow (v : RawWord) (m : ℕ) :
    rawWeight (rawNatPow v m) = m * rawWeight v := by
  induction m with
  | zero => simp [rawNatPow, rawWeight]
  | succ m ih =>
    rw [rawNatPow, rawWeight_append, ih, Nat.succ_mul]

/-- A minimal bad period cannot literally consist of two or more copies
of a nonempty word: the shorter word is good, hence so is its power. -/
theorem minBad_not_literal_power {N : Subgroup F} [N.Normal] {c : F}
    (hc : MinBad N c) (v : RawWord) (m : ℕ)
    (hv : v ≠ []) (hm : 2 ≤ m) :
    c.toWord ≠ rawNatPow v m := by
  intro heq
  have hpos : 0 < rawWeight v := by
    by_contra! hn
    exact hv ((rawWeight_eq_zero_iff v).mp (by omega))
  have hle := weightedLength_mk_le v
  have hweight : weightedLength c = m * rawWeight v := by
    unfold weightedLength
    rw [heq, rawWeight_rawNatPow]
  have hmul : 2 * rawWeight v ≤ m * rawWeight v :=
    Nat.mul_le_mul_right _ hm
  have hg : Good N (FreeGroup.mk v) :=
    minBad_shorter_good hc (by omega)
  have hpow : c = (FreeGroup.mk v)^m := by
    rw [← rawNatPow_eval, ← heq, FreeGroup.mk_toWord]
  apply hc.1
  rw [hpow]
  exact good_pow N hg m


/-! ## Coupled choice of special prefixes and quotient stages

The preceding algebraic construction allows arbitrary conjugators.
Here we explicitly retain the previous prefix weight in the recursive
state, so the next special prefix is chosen by both inequalities.
This is not yet the paper's full admissibility theorem or tie order.
-/

/-- Stage data: the normal subgroup and the weight of the last chosen
special prefix. At a stationary stage retain the previous weight. -/
noncomputable def gubaState (pick : WeightedSelector) :
    ℕ → Subgroup F × ℕ
  | 0 => (⊥, 0)
  | i+1 => by
    classical
    let S := gubaState pick i
    exact if h : ∃ w : F, ¬ Good S.1 w then
      let c := (pick S.1 h).val
      let q := gubaEvenPrefix (chooseEvenPrefixIndex c S.2)
      (adjoin S.1 (heightRelator (positiveWord (longRaw q (10^20))) c 1),
        positiveWeight q)
    else S

noncomputable def gubaConjugatorChoice (pick : WeightedSelector) : ConjugatorChoice :=
  fun i _ c =>
    positiveWord (longRaw
      (gubaEvenPrefix (chooseEvenPrefixIndex c (gubaState pick i).2)) (10^20))

theorem gubaState_stage (pick : WeightedSelector) (i : ℕ) :
    (gubaState pick i).1 = weightedStages pick (gubaConjugatorChoice pick) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    classical
    let step : Subgroup F → Subgroup F := fun N =>
      adjoin N (weightedRelator pick (gubaConjugatorChoice pick) i N)
    calc
      (gubaState pick (i+1)).1 = step (gubaState pick i).1 := by
        by_cases h : ∃ w : F, ¬ Good (gubaState pick i).1 w
        · simp only [gubaState, step, weightedRelator, dite_eq_left h,
            gubaConjugatorChoice]
        · simp only [gubaState, step, weightedRelator, dite_eq_right h]
          have hn := weightedStages_normal pick (gubaConjugatorChoice pick) i
          rw [← ih] at hn
          let _ : (gubaState pick i).1.Normal := hn
          exact (adjoin_eq_of_mem _ 1 (Subgroup.one_mem _)).symm
      _ = step (weightedStages pick (gubaConjugatorChoice pick) i) :=
        congrArg step ih
      _ = weightedStages pick (gubaConjugatorChoice pick) (i+1) := rfl

theorem gubaState_weight_mono (pick : WeightedSelector) :
    Monotone (fun i => (gubaState pick i).2) := by
  apply monotone_nat_of_le_succ
  intro i
  classical
  by_cases h : ∃ w : F, ¬ Good (gubaState pick i).1 w
  · simp only [gubaState, dite_eq_left h]
    have hs := chooseEvenPrefixIndex_spec ((pick (gubaState pick i).1 h).val)
      (gubaState pick i).2
    exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) hs)
  · simp only [gubaState, dite_eq_right h]
    exact le_rfl

theorem gubaState_active_weight_lt (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) :
    (gubaState pick i).2 < (gubaState pick (i+1)).2 := by
  classical
  simp only [gubaState, dite_eq_left h]
  exact lt_of_le_of_lt (le_max_right _ _)
    (chooseEvenPrefixIndex_spec ((pick (gubaState pick i).1 h).val) (gubaState pick i).2)

/-- At every active stage, the stored weight is exactly the weight
of the prefix used in the actual conjugator choice. -/
theorem gubaState_active_weight (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) :
    (gubaState pick (i+1)).2 =
      positiveWeight (gubaEvenPrefix
        (chooseEvenPrefixIndex ((pick (gubaState pick i).1 h).val) (gubaState pick i).2)) := by
  classical
  simp only [gubaState, dite_eq_left h]

/-- Distinct active stages have distinct special prefix weights.
Stationary stages need not have a new prefix, and are excluded. -/
theorem gubaState_active_weights_distinct (pick : WeightedSelector)
    {i j : ℕ} (hij : i < j)
    (hj : ∃ w : F, ¬ Good (gubaState pick j).1 w) :
    (gubaState pick (i+1)).2 < (gubaState pick (j+1)).2 :=
  lt_of_le_of_lt (gubaState_weight_mono pick (show i+1 ≤ j by omega))
    (gubaState_active_weight_lt pick j hj)


/-! ## Overlap estimates for the actual active ranks

Index the positive conjugating words by the stages and their proofs of
activity. The proof argument is a proposition; it does not introduce a
new choice of period or of prefix.
-/

noncomputable def activePrefix (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) : List (Fin 2) :=
  gubaEvenPrefix (chooseEvenPrefixIndex
    (pick (gubaState pick i).1 h).val (gubaState pick i).2)

noncomputable def activeLongWord (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) : List (Fin 2) :=
  longRaw (activePrefix pick i h) (10^20)

theorem activePrefix_weight (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) :
    positiveWeight (activePrefix pick i h) = (gubaState pick (i+1)).2 :=
  (gubaState_active_weight pick i h).symm

theorem activePrefix_weight_ge (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) :
    6*10^80 ≤ positiveWeight (activePrefix pick i h) :=
  chosenEvenPrefix_weight_ge _ _ (pick (gubaState pick i).1 h).property.1 _

theorem activePrefix_ne (pick : WeightedSelector) {i j : ℕ}
    (hi : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (hj : ∃ w : F, ¬ Good (gubaState pick j).1 w) (hij : i ≠ j) :
    activePrefix pick i hi ≠ activePrefix pick j hj := by
  intro he
  have hw := congrArg positiveWeight he
  rw [activePrefix_weight, activePrefix_weight] at hw
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (ne_of_lt (gubaState_active_weights_distinct pick hlt hj)) hw
  · exact (ne_of_gt (gubaState_active_weights_distinct pick hgt hi)) hw

/-- The literal word used for an active rank evaluates to the chosen
conjugator in the algebraic presentation. -/
theorem activeLongWord_eval (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w) :
    positiveWord (activeLongWord pick i h) =
      gubaConjugatorChoice pick i (gubaState pick i).1
        (pick (gubaState pick i).1 h).val :=
  rfl

/-- A common factor in actual active conjugators is short whenever
the ranks differ or the two positions differ. No additional
strict-prefix-growth hypothesis is required. -/
theorem activeLongWord_overlap_bound (pick : WeightedSelector) (i j : ℕ)
    (hi : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (hj : ∃ w : F, ¬ Good (gubaState pick j).1 w)
    (p z r u v : List (Fin 2))
    (hfirst : activeLongWord pick i hi = p ++ z ++ r)
    (hsecond : activeLongWord pick j hj = u ++ z ++ v)
    (hdiff : i ≠ j ∨ p.length ≠ u.length) :
    240*10^17*positiveWeight z ≤ positiveWeight (activeLongWord pick i hi) := by
  have hd : activePrefix pick i hi ≠ activePrefix pick j hj ∨
      p.length ≠ u.length := by
    rcases hdiff with h | h
    · exact Or.inl (activePrefix_ne pick hi hj h)
    · exact Or.inr h
  exact guba_long_overlap_bound _ _ p z r u v
    (activePrefix_weight_ge pick i hi) hfirst hsecond hd

/-- Both sides of the overlap estimate for two actual active ranks. -/
theorem activeLongWord_overlap_bound_both (pick : WeightedSelector) (i j : ℕ)
    (hi : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (hj : ∃ w : F, ¬ Good (gubaState pick j).1 w)
    (p z r u v : List (Fin 2))
    (hfirst : activeLongWord pick i hi = p ++ z ++ r)
    (hsecond : activeLongWord pick j hj = u ++ z ++ v)
    (hdiff : i ≠ j ∨ p.length ≠ u.length) :
    240*10^17*positiveWeight z ≤
      min (positiveWeight (activeLongWord pick i hi))
        (positiveWeight (activeLongWord pick j hj)) := by
  apply le_min
  · exact activeLongWord_overlap_bound pick i j hi hj p z r u v hfirst hsecond hdiff
  · apply activeLongWord_overlap_bound pick j i hj hi u z v p r hsecond hfirst
    rcases hdiff with h | h
    · exact Or.inl (Ne.symm h)
    · exact Or.inr (Ne.symm h)


/-! ## Replacement of a minimal-period segment through earlier ranks

A minimal bad period is a shortest representative in the preceding
quotient. Hence every literal factor admits no shorter representative
there either. This is a necessary length comparison for a lower-rank
contiguity path; it makes no assumption of a particular diagram.
-/

/-- A two-sided boundary relation in a normal subgroup identifies the
two path readings in the quotient. -/
theorem quotient_paths_eq {N : Subgroup F} [N.Normal] (v u : RawWord)
    (h : FreeGroup.mk (v ++ FreeGroup.invRev u) ∈ N) :
    QuotientGroup.mk' N (FreeGroup.mk v) =
      QuotientGroup.mk' N (FreeGroup.mk u) := by
  have he := (QuotientGroup.eq_one_iff _).mpr h
  change QuotientGroup.mk' N (FreeGroup.mk (v ++ FreeGroup.invRev u)) = 1 at he
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv] at he
  calc
    _ = (QuotientGroup.mk' N (FreeGroup.mk v) *
          (QuotientGroup.mk' N (FreeGroup.mk u))⁻¹) *
          QuotientGroup.mk' N (FreeGroup.mk u) := by group
    _ = _ := by rw [he, one_mul]

/-- Every literal factor of a chosen minimal bad word is weight-minimal
among all words with the same value in the preceding quotient. -/
theorem minBad_factor_weight_min {N : Subgroup F} [N.Normal] {c : F}
    (hc : MinBad N c) (p v r u : RawWord)
    (hword : c.toWord = p ++ v ++ r)
    (heq : QuotientGroup.mk' N (FreeGroup.mk v) =
      QuotientGroup.mk' N (FreeGroup.mk u)) :
    rawWeight v ≤ rawWeight u := by
  have hreplace : QuotientGroup.mk' N c =
      QuotientGroup.mk' N (FreeGroup.mk (p ++ u ++ r)) := by
    calc
      _ = QuotientGroup.mk' N (FreeGroup.mk (p ++ v ++ r)) := by
        rw [← hword, FreeGroup.mk_toWord]
      _ = _ := by simp only [← FreeGroup.mul_mk, map_mul, heq]
  have hmin := minBad_quotient_length hc hreplace
  have hle := weightedLength_mk_le (p ++ u ++ r)
  have hweight : weightedLength c = rawWeight p + rawWeight v + rawWeight r := by
    unfold weightedLength
    rw [hword, rawWeight_append, rawWeight_append]
  rw [rawWeight_append, rawWeight_append] at hle
  omega

/-- The same comparison when the two paths bound a word trivial at
lower rank. The normal subgroup membership is the algebraic boundary
condition, not an assumption that the paths are geometrically adjacent. -/
theorem minBad_factor_boundary_weight {N : Subgroup F} [N.Normal] {c : F}
    (hc : MinBad N c) (p v r u : RawWord)
    (hword : c.toWord = p ++ v ++ r)
    (hboundary : FreeGroup.mk (v ++ FreeGroup.invRev u) ∈ N) :
    rawWeight v ≤ rawWeight u :=
  minBad_factor_weight_min hc p v r u hword (quotient_paths_eq v u hboundary)

/-- Instantiate the replacement inequality with the actual selected
period and any all-height presentation of earlier ranks. -/
theorem activePeriod_factor_boundary_weight (pick : WeightedSelector)
    (i j : ℕ) (hji : j ≤ i)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (p v r u : RawWord)
    (hword : (pick (gubaState pick i).1 h).val.toWord = p ++ v ++ r)
    (hboundary : FreeGroup.mk (v ++ FreeGroup.invRev u) ∈
      weightedHeightStage pick (gubaConjugatorChoice pick) j) :
    rawWeight v ≤ rawWeight u := by
  have hn := weightedStages_normal pick (gubaConjugatorChoice pick) i
  rw [← gubaState_stage pick i] at hn
  let _ : (gubaState pick i).1.Normal := hn
  apply minBad_factor_boundary_weight (pick (gubaState pick i).1 h).property p v r u hword
  rw [gubaState_stage pick i]
  rw [weightedHeightStage_eq] at hboundary
  exact weightedStages_mono pick (gubaConjugatorChoice pick) hji hboundary

end QuandleResearch.Issue070
