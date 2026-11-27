import QuandleResearch.Proofs.Kourovka88a.Greedy
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Word-level infrastructure for Guba's construction

The weighted lengths use the integral rescaling of |a| = 10^(-80),
|b| = 1 recorded in issue #70. This module does not assert that a
specific tie ordering or a sequence of long words is admissible for
Guba's graded diagram lemmas. The exact source transcription and
all geometric hypotheses still need an independent audit.

We use Mathlib's reduced-word representation of the free group.
Raw words and reduced free-group elements are kept distinct.
-/

namespace QuandleResearch.Issue070

abbrev Letter := Fin 2 × Bool
abbrev RawWord := List Letter

/-- Integral letter weight (sign does not matter). -/
def letterWeight (x : Letter) : ℕ :=
  if x.1 = 0 then 1 else 10 ^ 80

def rawWeight : RawWord → ℕ
  | [] => 0
  | x :: xs => letterWeight x + rawWeight xs

def weightedLength (w : F) : ℕ := rawWeight w.toWord

theorem letterWeight_pos (x : Letter) : 0 < letterWeight x := by
  unfold letterWeight
  split <;> norm_num

theorem rawWeight_append (u v : RawWord) :
    rawWeight (u ++ v) = rawWeight u + rawWeight v := by
  induction u with
  | nil => simp [rawWeight]
  | cons x xs ih => simp [rawWeight, ih, Nat.add_assoc]

theorem length_le_rawWeight (w : RawWord) : w.length ≤ rawWeight w := by
  induction w with
  | nil => simp [rawWeight]
  | cons x xs ih =>
      have hp := letterWeight_pos x
      simp only [List.length_cons, rawWeight]
      omega

theorem rawWeight_eq_zero_iff (w : RawWord) : rawWeight w = 0 ↔ w = [] := by
  constructor
  · intro h
    have hl := length_le_rawWeight w
    cases w with
    | nil => rfl
    | cons x xs => simp at hl; omega
  · rintro rfl
    rfl

theorem weightedLength_eq_zero_iff (w : F) : weightedLength w = 0 ↔ w = 1 := by
  rw [weightedLength, rawWeight_eq_zero_iff, FreeGroup.toWord_eq_nil_iff]

/-- The four signed generators. -/
def letters : List Letter := [(0,true), (0,false), (1,true), (1,false)]

theorem mem_letters (x : Letter) : x ∈ letters := by
  rcases x with ⟨i,s⟩
  fin_cases i <;> cases s <;> decide

/-- Explicit finite lists of all raw words of length at most n.
Duplicates, if any, do not affect completeness. -/
def boundedWords : ℕ → List RawWord
  | 0 => [[]]
  | n + 1 =>
      [] :: letters.flatMap (fun x => (boundedWords n).map (List.cons x))

theorem mem_boundedWords (n : ℕ) (w : RawWord) :
    w ∈ boundedWords n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
      cases w <;> simp [boundedWords]
  | succ n ih =>
      cases w with
      | nil => simp [boundedWords]
      | cons x xs =>
          constructor
          · intro hw
            simp only [boundedWords, List.mem_cons, List.cons_ne_nil, false_or] at hw
            obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hw
            obtain ⟨ys, hys, heq⟩ := List.mem_map.mp hy
            cases heq
            have h := (ih _).mp hys
            simpa using Nat.succ_le_succ h
          · intro hw
            have hxs : xs.length ≤ n := by simpa using hw
            exact List.mem_cons_of_mem _
              (List.mem_flatMap.mpr ⟨x, mem_letters x,
                List.mem_map.mpr ⟨xs, (ih _).mpr hxs, rfl⟩⟩)

/-- A finite list covering the entire weighted ball. This is the
finiteness input needed for choosing a weighted-length-first order. -/
def weightedBallCover (n : ℕ) : List F :=
  (boundedWords n).map FreeGroup.mk

theorem mem_weightedBallCover (n : ℕ) (w : F) (hw : weightedLength w ≤ n) :
    w ∈ weightedBallCover n := by
  apply List.mem_map.mpr
  refine ⟨w.toWord, (mem_boundedWords n _).mpr ?_, FreeGroup.mk_toWord⟩
  exact (length_le_rawWeight w.toWord).trans hw

/-- An exact integer weight of the fixed commutator, after free reduction. -/
theorem weightedLength_commWord :
    weightedLength commWord = 2 + 2 * 10 ^ 80 := by
  have hw : commWord.toWord =
      ([(0,true),(1,true),(0,false),(1,false)] : RawWord) := by
    decide
  rw [weightedLength, hw]
  norm_num [rawWeight, letterWeight]

theorem commWord_ne_one : commWord ≠ 1 := by
  intro h
  have hz := (weightedLength_eq_zero_iff commWord).2 h
  rw [weightedLength_commWord] at hz
  norm_num at hz

/-- The final survival interface in terms of a weighted injectivity bound.
It is enough to exclude nonidentity elements up to the commutator weight.
The bound is a hypothesis, NOT Guba's proved diagram estimate. -/
theorem answer_of_weighted_survival (words X : ℕ → F)
    (hwords : Function.Surjective words)
    (hshort : ∀ i w, w ∈ greedyStages words X i →
      weightedLength w ≤ 2 + 2 * 10 ^ 80 → w = 1) : answer := by
  apply answer_of_greedyStages words X hwords
  intro i hi
  exact commWord_ne_one (hshort i commWord hi weightedLength_commWord.le)

/-- Positive words are supplied as lists of generator indices. -/
def positiveWord (q : List (Fin 2)) : F :=
  FreeGroup.mk (q.map (fun x => (x, true)))

/-- Candidate long-conjugator formula from the source transcription in
issue #70, with a parameter for the number of blocks. No admissibility
or small-cancellation property is asserted here. -/
def longConjugator (q : F) (blocks : ℕ) : F :=
  ((List.range blocks).map (fun j => b ^ (3 : ℕ) * q ^ (j + 1))).prod

end QuandleResearch.Issue070
