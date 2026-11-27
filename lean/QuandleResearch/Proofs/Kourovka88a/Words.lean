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
  exact commWord_ne_one (hshort i commWord hi (le_of_eq weightedLength_commWord))

/-- Positive words are supplied as lists of generator indices. -/
def positiveWord (q : List (Fin 2)) : F :=
  FreeGroup.mk (q.map (fun x => (x, true)))

/-- Candidate long-conjugator formula from the source transcription in
issue #70, with a parameter for the number of blocks. No admissibility
or small-cancellation property is asserted here. -/
def longConjugator (q : F) (blocks : ℕ) : F :=
  ((List.range blocks).map (fun j => b ^ (3 : ℕ) * q ^ (j + 1))).prod


/-- Deleting letters never increases the integral weight. -/
theorem rawWeight_le_of_sublist {u v : RawWord} (h : u.Sublist v) :
    rawWeight u ≤ rawWeight v := by
  induction h with
  | slnil => exact Nat.le_refl 0
  | cons x h ih =>
    have hx := letterWeight_pos x
    simp only [rawWeight]
    omega
  | cons_cons x h ih =>
    simp only [rawWeight]
    omega

/-- Free reduction can only decrease weighted length. -/
theorem weightedLength_mk_le (w : RawWord) :
    weightedLength (FreeGroup.mk w) ≤ rawWeight w := by
  rw [weightedLength, FreeGroup.toWord_mk]
  exact rawWeight_le_of_sublist (FreeGroup.Red.sublist FreeGroup.reduce.red)

theorem weightedLength_mul_le (u v : F) :
    weightedLength (u * v) ≤ weightedLength u + weightedLength v := by
  unfold weightedLength
  rw [← rawWeight_append]
  exact rawWeight_le_of_sublist (FreeGroup.toWord_mul_sublist u v)

/-- A positive word is already freely reduced: adjacent positive
letters cannot form an inverse pair. -/
theorem reduce_positive (q : List (Fin 2)) :
    FreeGroup.reduce (q.map (fun x => (x, true))) =
      q.map (fun x => (x, true)) := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    rw [List.map_cons, FreeGroup.reduce.cons, ih]
    cases q <;> simp

theorem toWord_positiveWord (q : List (Fin 2)) :
    (positiveWord q).toWord = q.map (fun x => (x, true)) := by
  rw [positiveWord, FreeGroup.toWord_mk, reduce_positive]

theorem positiveWord_append (p q : List (Fin 2)) :
    positiveWord (p ++ q) = positiveWord p * positiveWord q := by
  unfold positiveWord
  rw [List.map_append, ← FreeGroup.mul_mk]

/-- There is no loss of weight on concatenating positive words. -/
theorem weightedLength_positive_mul (p q : List (Fin 2)) :
    weightedLength (positiveWord p * positiveWord q) =
      weightedLength (positiveWord p) + weightedLength (positiveWord q) := by
  rw [← positiveWord_append]
  simp only [weightedLength, toWord_positiveWord, List.map_append, rawWeight_append]

theorem rawWeight_replicate (n : ℕ) (x : Letter) :
    rawWeight (List.replicate n x) = n * letterWeight x := by
  induction n with
  | zero => simp [rawWeight]
  | succ n ih =>
    rw [List.replicate_succ, rawWeight, ih, Nat.succ_mul, Nat.add_comm]

/-- Exact weight of an arbitrary signed power of the short generator. -/
theorem weightedLength_a_zpow (k : ℤ) : weightedLength (a ^ k) = k.natAbs := by
  simp [weightedLength, a, FreeGroup.toWord_of_zpow, rawWeight_replicate,
    letterWeight]

/-- Exact weight of an arbitrary signed power of the long generator. -/
theorem weightedLength_b_zpow (k : ℤ) :
    weightedLength (b ^ k) = k.natAbs * 10 ^ 80 := by
  have hb : (1 : Fin 2) ≠ 0 := by decide
  simp only [weightedLength, b, FreeGroup.toWord_of_zpow, rawWeight_replicate,
    letterWeight, ite_eq_right hb]

/-- Repeating a positive raw word realizes powers without cancellation. -/
theorem positiveWord_repeat (q : List (Fin 2)) (n : ℕ) :
    positiveWord (List.replicate n q).flatten = positiveWord q ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, positiveWord_append, ih, pow_succ']

/-- Weight grows exactly linearly under positive powers. -/
theorem weightedLength_positive_pow (q : List (Fin 2)) (n : ℕ) :
    weightedLength (positiveWord q ^ n) = n * weightedLength (positiveWord q) := by
  induction n with
  | zero => simp [weightedLength, FreeGroup.toWord_one, rawWeight]
  | succ n ih =>
    rw [pow_succ', ← positiveWord_repeat q n, weightedLength_positive_mul,
      positiveWord_repeat, ih, Nat.succ_mul, Nat.add_comm]

/-- Positive raw blocks for the candidate long-conjugator formula.
This is not a proof of Guba's overlap restrictions. -/
def longBlock (q : List (Fin 2)) (j : ℕ) : List (Fin 2) :=
  List.replicate 3 1 ++ (List.replicate (j+1) q).flatten

theorem positiveWord_longBlock (q : List (Fin 2)) (j : ℕ) :
    positiveWord (longBlock q j) = b ^ (3 : ℕ) * positiveWord q ^ (j+1) := by
  rw [longBlock, positiveWord_append, positiveWord_repeat]
  have hb : positiveWord (List.replicate 3 (1 : Fin 2)) = b ^ (3 : ℕ) := by decide
  rw [hb]

theorem weightedLength_longBlock (q : List (Fin 2)) (j : ℕ) :
    weightedLength (positiveWord (longBlock q j)) =
      3 * 10 ^ 80 + (j+1) * weightedLength (positiveWord q) := by
  rw [longBlock, positiveWord_append, weightedLength_positive_mul, positiveWord_repeat,
    weightedLength_positive_pow]
  have hb : weightedLength (positiveWord (List.replicate 3 (1 : Fin 2))) =
      3 * 10 ^ 80 := by
    rw [weightedLength, toWord_positiveWord]
    norm_num [rawWeight, letterWeight]
  rw [hb]

end QuandleResearch.Issue070
