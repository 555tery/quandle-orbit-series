import QuandleResearch.Questions.Issue070
import Mathlib.Data.Nat.Find

/-!
# Greedy recursion for the algebraic part of Kourovka 8.8(a)

We construct the actual recursive sequence of normal subgroups for an
arbitrary enumeration and an arbitrary sequence of conjugating words.
Classical choice is used to find the least bad index; no claim of an
effective algorithm or of geometric survival is made.

Guba's specific weighted order and long-word choices are a further
specialization. In particular, arbitrary conjugators need not preserve
the commutator.
-/

namespace QuandleResearch.Issue070

noncomputable section

/-- The next relation makes the least bad word conjugate to a itself.
If there are no bad words, no new relation is imposed. -/
def nextRelator (words : ℕ → F) (N : Subgroup F) (X : F) : F := by
  classical
  exact if h : ∃ j, ¬ Good N (words j) then
    X * words (Nat.find h) * X⁻¹ * a⁻¹
  else 1

theorem nextRelator_eq (words : ℕ → F) (N : Subgroup F) (X : F)
    (j : ℕ) (hbad : ¬ Good N (words j))
    (hprev : ∀ k < j, Good N (words k)) :
    nextRelator words N X = X * words j * X⁻¹ * a⁻¹ := by
  classical
  have hex : ∃ k, ¬ Good N (words k) := ⟨j, hbad⟩
  have hmin : Nat.find hex = j := by
    apply (Nat.find_eq_iff hex).2
    exact ⟨hbad, fun k hk h => h (hprev k hk)⟩
  simp only [nextRelator, dite_eq_left hex, hmin]

theorem nextRelator_eq_one (words : ℕ → F) (N : Subgroup F) (X : F)
    (hall : ∀ j, Good N (words j)) :
    nextRelator words N X = 1 := by
  classical
  have hnone : ¬ ∃ j, ¬ Good N (words j) := by
    rintro ⟨j, hj⟩
    exact hj (hall j)
  simp only [nextRelator, dite_eq_right hnone]

/-- Adjoin one relation by taking a normal closure in the original free
group, rather than changing the ambient type at every rank. -/
def adjoin (N : Subgroup F) (r : F) : Subgroup F :=
  Subgroup.normalClosure ((N : Set F) ∪ {r})

instance adjoinNormal (N : Subgroup F) (r : F) : (adjoin N r).Normal := by
  unfold adjoin
  infer_instance

theorem le_adjoin (N : Subgroup F) (r : F) : N ≤ adjoin N r := by
  intro w hw
  exact Subgroup.subset_normalClosure (Or.inl hw)

theorem relator_mem_adjoin (N : Subgroup F) (r : F) : r ∈ adjoin N r :=
  Subgroup.subset_normalClosure (Or.inr rfl)

/-- If the new relation is already in a normal subgroup, adjoining it
does not enlarge that subgroup. -/
theorem adjoin_eq_of_mem (N : Subgroup F) [N.Normal] (r : F) (hr : r ∈ N) :
    adjoin N r = N := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro w hw
    rcases hw with hw | hw
    · exact hw
    · have h : w = r := hw
      simpa only [h] using hr
  · exact le_adjoin N r

/-- Stage zero is the trivial normal subgroup of the free group.
This is the rank-one base with no relators in Guba's specialization.
The next stages need not be nontrivial quotients. -/
def greedyStages (words X : ℕ → F) : ℕ → Subgroup F
  | 0 => ⊥
  | n + 1 =>
      adjoin (greedyStages words X n)
        (nextRelator words (greedyStages words X n) (X n))

theorem greedyStages_normal (words X : ℕ → F) (n : ℕ) :
    (greedyStages words X n).Normal := by
  cases n with
  | zero =>
    change (⊥ : Subgroup F).Normal
    infer_instance
  | succ n =>
    change (adjoin _ _).Normal
    infer_instance

theorem greedyStages_mono (words X : ℕ → F) :
    Monotone (greedyStages words X) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_adjoin _ _

/-- The greedy step always repairs the chosen word, regardless of X. -/
theorem greedyStages_progress (words X : ℕ → F) (i j : ℕ)
    (hbad : ¬ Good (greedyStages words X i) (words j))
    (hprev : ∀ k < j, Good (greedyStages words X i) (words k)) :
    Good (greedyStages words X (i + 1)) (words j) := by
  refine ⟨X i, 1, ?_⟩
  rw [zpow_one]
  change X i * words j * (X i)⁻¹ * a⁻¹ ∈
    adjoin (greedyStages words X i)
      (nextRelator words (greedyStages words X i) (X i))
  rw [← nextRelator_eq words (greedyStages words X i) (X i) j hbad hprev]
  exact relator_mem_adjoin _ _

/-- A genuinely bad word makes the inclusion of normal subgroups strict.
This must NOT be confused with properness inside the whole free group:
the new stage might still be the whole free group. -/
theorem greedyStages_strict_of_bad (words X : ℕ → F) (i j : ℕ)
    (hbad : ¬ Good (greedyStages words X i) (words j))
    (hprev : ∀ k < j, Good (greedyStages words X i) (words k)) :
    greedyStages words X i < greedyStages words X (i + 1) := by
  apply lt_of_le_of_ne (greedyStages_mono words X (Nat.le_succ i))
  intro heq
  exact hbad (heq.symm ▸ greedyStages_progress words X i j hbad hprev)

/-- The recursion freezes if every enumerated word is already good. -/
theorem greedyStages_stationary (words X : ℕ → F) (i : ℕ)
    (hall : ∀ j, Good (greedyStages words X i) (words j)) :
    greedyStages words X (i + 1) = greedyStages words X i := by
  let _ : (greedyStages words X i).Normal := greedyStages_normal words X i
  change adjoin (greedyStages words X i)
    (nextRelator words (greedyStages words X i) (X i)) = greedyStages words X i
  rw [nextRelator_eq_one words (greedyStages words X i) (X i) hall]
  exact adjoin_eq_of_mem _ 1 (Subgroup.one_mem _)

/-- Coverage is now a theorem of the recursive definition, not a
hypothesis on a purported list of relators. -/
theorem greedyStages_cover (words X : ℕ → F)
    (hwords : Function.Surjective words) :
    ∀ w : F, ∃ i, Good (greedyStages words X i) w := by
  exact greedy_cover (greedyStages words X) (greedyStages_mono words X)
    words hwords (greedyStages_progress words X)

/-- The remaining mathematical input is survival for some choice of
enumeration and conjugators. This conditional theorem is not an
unconditional proof of 8.8(a). -/
theorem answer_of_greedyStages (words X : ℕ → F)
    (hwords : Function.Surjective words)
    (hsurvive : ∀ i, commWord ∉ greedyStages words X i) : answer := by
  exact answer_of_chain (greedyStages words X) (greedyStages_mono words X)
    (greedyStages_normal words X) hsurvive (greedyStages_cover words X hwords)

end

end QuandleResearch.Issue070
