import QuandleResearch.Proofs.Kourovka88a.Greedy
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.List.PeriodicityLemma

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


/-! ## A cube-free infinite binary word

We prove cube-freeness from the even/odd recurrences, without importing
a combinatorics-on-words existence axiom. This supplies a candidate
infinite positive word; Guba's further restrictions on prefixes and
overlaps still have to be checked against the original construction.
-/

/-- Three consecutive equal nonempty blocks of period d, starting at p.
The pointwise formulation avoids unnecessary list indexing proofs. -/
def CubeAt (s : ℕ → Bool) (p d : ℕ) : Prop :=
  ∀ j < 2 * d, s (p + j) = s (p + j + d)

/-- In a sequence with complementary pairs at even indices, an equal
adjacent pair can start only at an odd index. -/
theorem adjacent_eq_odd (s : ℕ → Bool)
    (heven : ∀ n, s (2*n) = s n)
    (hodd : ∀ n, s (2*n+1) = !(s n))
    (t : ℕ) (h : s t = s (t+1)) : t % 2 = 1 := by
  by_contra hn
  have ht : t = 2 * (t/2) := by omega
  have ht1 : t+1 = 2 * (t/2)+1 := by omega
  rw [ht1] at h
  have hleft : s t = s (t/2) := by
    calc
      s t = s (2*(t/2)) := congrArg s ht
      _ = s (t/2) := heven _
  rw [hleft, hodd] at h
  cases hs : s (t/2) <;> simp [hs] at h

/-- A cube of odd positive period would force its first block to
alternate, but an odd number of alternations contradicts periodicity. -/
theorem no_odd_cube (s : ℕ → Bool)
    (heven : ∀ n, s (2*n) = s n)
    (hodd : ∀ n, s (2*n+1) = !(s n))
    (p d : ℕ) (hd : d % 2 = 1) : ¬ CubeAt s p d := by
  intro hc
  have hstep : ∀ j < d, s (p+j+1) = !(s (p+j)) := by
    intro j hj
    have h0 := hc j (by omega)
    have h1 := hc (j+1) (by omega)
    have hne : s (p+j) ≠ s (p+j+1) := by
      intro heq
      have heq' : s (p+j+d) = s (p+j+d+1) := by
        calc
          _ = s (p+j) := h0.symm
          _ = s (p+j+1) := heq
          _ = s (p+(j+1)+d) := h1
          _ = _ := congrArg s (by omega)
      have hleft := adjacent_eq_odd s heven hodd (p+j) heq
      have hright := adjacent_eq_odd s heven hodd (p+j+d) heq'
      omega
    cases hx : s (p+j) <;> cases hy : s (p+j+1) <;> simp_all
  have halt : ∀ j ≤ d, s (p+j) =
      if j % 2 = 0 then s p else !(s p) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hrec := ih (by omega)
      have hflip := hstep j (by omega)
      have hidx : p+(j+1) = p+j+1 := by omega
      rw [hidx, hflip, hrec]
      by_cases hj' : j % 2 = 0
      · have hs : (j+1) % 2 ≠ 0 := by omega
        simp [hj', hs]
      · have hs : (j+1) % 2 = 0 := by omega
        simp [hj', hs]
  have hfirst := hc 0 (by omega)
  have hlast := halt d le_rfl
  have hne : d % 2 ≠ 0 := by omega
  simp only [Nat.add_zero] at hfirst
  simp [hne] at hlast
  have hb : s p = !(s p) := hfirst.trans hlast
  cases hs : s p <;> simp [hs] at hb

/-- A cube of even period descends to a cube of half the period by
taking every second letter; both parities of the starting index work. -/
theorem cube_even_descend (s : ℕ → Bool)
    (heven : ∀ n, s (2*n) = s n)
    (hodd : ∀ n, s (2*n+1) = !(s n))
    (p d : ℕ) (hd : d % 2 = 0) (hc : CubeAt s p d) :
    CubeAt s (p/2) (d/2) := by
  intro j hj
  have hh := hc (2*j) (by omega)
  by_cases hp : p % 2 = 0
  · have h0 : p+2*j = 2*(p/2+j) := by omega
    have h1 : p+2*j+d = 2*(p/2+j+d/2) := by omega
    rw [h1, h0] at hh
    simpa only [heven] using hh
  · have h0 : p+2*j = 2*(p/2+j)+1 := by omega
    have h1 : p+2*j+d = 2*(p/2+j+d/2)+1 := by omega
    rw [h1, h0] at hh
    simpa [hodd] using hh

/-- A least positive cube period is impossible: odd periods are
excluded directly, and even periods contradict minimality. -/
theorem cubeFree_of_binary_rec (s : ℕ → Bool)
    (heven : ∀ n, s (2*n) = s n)
    (hodd : ∀ n, s (2*n+1) = !(s n)) :
    ∀ p d : ℕ, 0 < d → ¬ CubeAt s p d := by
  classical
  intro p d hd hc
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ q, CubeAt s q n := ⟨d, hd, p, hc⟩
  obtain ⟨hm, q, hq⟩ := Nat.find_spec hex
  let m := Nat.find hex
  change 0 < m at hm
  change CubeAt s q m at hq
  by_cases hpar : m % 2 = 0
  · have hpos : 0 < m/2 := by omega
    have hsmall : m/2 < m := by omega
    have hcube := cube_even_descend s heven hodd q m hpar hq
    have hmin : m ≤ m/2 := Nat.find_min' hex ⟨hpos, q/2, hcube⟩
    omega
  · exact no_odd_cube s heven hodd q m (by omega) hq

/-- The Thue–Morse word, using parity of binary digits recursively. -/
def thueMorse (n : ℕ) : Bool :=
  if h : n = 0 then false
  else if n % 2 = 0 then thueMorse (n/2)
  else !(thueMorse (n/2))
termination_by n
decreasing_by all_goals omega

theorem thueMorse_even (n : ℕ) : thueMorse (2*n) = thueMorse n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have h0 : 2*n ≠ 0 := by omega
    have hp : (2*n) % 2 = 0 := by omega
    have hdiv : (2*n)/2 = n := by omega
    conv_lhs => rw [thueMorse]
    simp [h0, hp, hdiv]

theorem thueMorse_odd (n : ℕ) : thueMorse (2*n+1) = !(thueMorse n) := by
  have hdiv : (2*n+1)/2 = n := by omega
  conv_lhs => rw [thueMorse]
  simp [hdiv]

theorem thueMorse_cubeFree (p d : ℕ) (hd : 0 < d) :
    ¬ CubeAt thueMorse p d :=
  cubeFree_of_binary_rec thueMorse thueMorse_even thueMorse_odd p d hd


/-- The two Boolean symbols as positive generator indices. -/
def thueLetter (n : ℕ) : Fin 2 := if thueMorse n then 1 else 0

theorem thueLetter_eq_iff (i j : ℕ) :
    thueLetter i = thueLetter j ↔ thueMorse i = thueMorse j := by
  unfold thueLetter
  cases thueMorse i <;> cases thueMorse j <;> decide

/-- Every finite prefix is an actual finite positive word in a,b. -/
def thuePrefix (n : ℕ) : List (Fin 2) :=
  List.ofFn (fun i : Fin n => thueLetter i.val)

theorem thuePrefix_length (n : ℕ) : (thuePrefix n).length = n := by
  simp [thuePrefix]

theorem thuePrefix_get (n i : ℕ) (hi : i < (thuePrefix n).length) :
    (thuePrefix n)[i] = thueLetter i := by
  simp [thuePrefix]

/-- A triple repetition cannot occur inside any finite prefix.
Both compared positions are required to be within that prefix. -/
theorem thuePrefix_cubeFree (n p d : ℕ) (hd : 0 < d) (hfit : p+3*d ≤ n) :
    ¬ (∀ (j : ℕ) (hj : j < 2*d),
      (thuePrefix n)[p+j]'(by rw [thuePrefix_length]; omega) =
        (thuePrefix n)[p+j+d]'(by rw [thuePrefix_length]; omega)) := by
  intro hc
  apply thueMorse_cubeFree p d hd
  intro j hj
  exact (thueLetter_eq_iff _ _).mp (by simpa only [thuePrefix_get] using hc j hj)


/-! ## Choosing the successive odd-length prefixes

Source: Guba, Math. USSR-Izv. 29 (1987), pp. 234, 238, 277.
T_1,T_2,... are successive odd-letter-length prefixes ending in a,
starting with a prefix containing both letters. Q_i is chosen from
T_2,T_4,... by a least-index weight condition. The construction below
uses the concrete Thue–Morse word, starting a,b. It does not yet prove
the resolvent uniqueness or graded-diagram estimates.
-/

/-- Zero-based last index of an odd-length prefix ending in a and
containing both initial letters. -/
def EligiblePrefixEnd (n : ℕ) : Prop :=
  n % 2 = 0 ∧ thueMorse n = false ∧ 1 < n

theorem exists_eligiblePrefixEnd_after (bound : ℕ) :
    ∃ n, bound < n ∧ EligiblePrefixEnd n := by
  let k := bound + 1
  have h0 : thueMorse (4*k) = thueMorse k := by
    rw [show 4*k = 2*(2*k) by omega, thueMorse_even, thueMorse_even]
  have h2 : thueMorse (4*k+2) = !(thueMorse k) := by
    rw [show 4*k+2 = 2*(2*k+1) by omega, thueMorse_even, thueMorse_odd]
  cases hk : thueMorse k with
  | false =>
    refine ⟨4*k, ?_, ?_, h0.trans hk, ?_⟩ <;> dsimp [k] <;> omega
  | true =>
    refine ⟨4*k+2, ?_, ?_, ?_, ?_⟩
    · dsimp [k]; omega
    · omega
    · rw [h2, hk]; rfl
    · dsimp [k]; omega

noncomputable def nextPrefixEnd (bound : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_eligiblePrefixEnd_after bound)

theorem nextPrefixEnd_spec (bound : ℕ) :
    bound < nextPrefixEnd bound ∧ EligiblePrefixEnd (nextPrefixEnd bound) := by
  classical
  exact Nat.find_spec (exists_eligiblePrefixEnd_after bound)

theorem nextPrefixEnd_min (bound n : ℕ)
    (h : bound < n ∧ EligiblePrefixEnd n) : nextPrefixEnd bound ≤ n := by
  classical
  exact Nat.find_min' (exists_eligiblePrefixEnd_after bound) h

/-- Index zero represents T_1, not T_0. -/
noncomputable def prefixEnd : ℕ → ℕ
  | 0 => nextPrefixEnd 1
  | m+1 => nextPrefixEnd (prefixEnd m)

theorem prefixEnd_eligible (m : ℕ) : EligiblePrefixEnd (prefixEnd m) := by
  cases m with
  | zero => exact (nextPrefixEnd_spec 1).2
  | succ m => exact (nextPrefixEnd_spec (prefixEnd m)).2

theorem prefixEnd_lt_succ (m : ℕ) : prefixEnd m < prefixEnd (m+1) :=
  (nextPrefixEnd_spec (prefixEnd m)).1

theorem prefixEnd_gt_index (m : ℕ) : m < prefixEnd m := by
  induction m with
  | zero => exact (Nat.zero_lt_one.trans (nextPrefixEnd_spec 1).1)
  | succ m ih =>
    have h := prefixEnd_lt_succ m
    omega

noncomputable def gubaPrefix (m : ℕ) : List (Fin 2) :=
  thuePrefix (prefixEnd m + 1)

/-- T_{2(m+1)} in the paper's one-based indexing. -/
noncomputable def gubaEvenPrefix (m : ℕ) : List (Fin 2) :=
  gubaPrefix (2*m+1)

theorem gubaPrefix_odd_length (m : ℕ) : (gubaPrefix m).length % 2 = 1 := by
  rw [gubaPrefix, thuePrefix_length]
  have h := (prefixEnd_eligible m).1
  omega

theorem gubaPrefix_last (m : ℕ) :
    (gubaPrefix m)[prefixEnd m]'(by rw [gubaPrefix, thuePrefix_length]; omega) = 0 := by
  change (thuePrefix (prefixEnd m+1))[prefixEnd m]'(by rw [thuePrefix_length]; omega) = 0
  rw [thuePrefix_get]
  simp [thueLetter, (prefixEnd_eligible m).2.1]

theorem gubaPrefix_first (m : ℕ) :
    (gubaPrefix m)[0]'(by rw [gubaPrefix, thuePrefix_length]; omega) = 0 := by
  change (thuePrefix (prefixEnd m+1))[0]'(by rw [thuePrefix_length]; omega) = 0
  rw [thuePrefix_get]
  have h : thueMorse 0 = false := by simp [thueMorse]
  simp [thueLetter, h]

theorem gubaPrefix_second (m : ℕ) :
    (gubaPrefix m)[1]'(by rw [gubaPrefix, thuePrefix_length]; have h := (prefixEnd_eligible m).2.2; omega) = 1 := by
  change (thuePrefix (prefixEnd m+1))[1]'(by rw [thuePrefix_length]; have h := (prefixEnd_eligible m).2.2; omega) = 1
  rw [thuePrefix_get]
  have h : thueMorse 1 = true := by
    have h0 : thueMorse 0 = false := by simp [thueMorse]
    simpa [h0] using thueMorse_odd 0
  simp [thueLetter, h]

theorem positiveWord_length_le (q : List (Fin 2)) :
    q.length ≤ weightedLength (positiveWord q) := by
  have h := length_le_rawWeight ((positiveWord q).toWord)
  change ((positiveWord q).toWord).length ≤ weightedLength (positiveWord q) at h
  rw [toWord_positiveWord, List.length_map] at h
  exact h

theorem exists_gubaEvenPrefix_weight_gt (bound : ℕ) :
    ∃ m, bound < weightedLength (positiveWord (gubaEvenPrefix m)) := by
  refine ⟨bound, ?_⟩
  have h := positiveWord_length_le (gubaEvenPrefix bound)
  have hi := prefixEnd_gt_index (2*bound+1)
  rw [gubaEvenPrefix, gubaPrefix, thuePrefix_length] at h
  rw [gubaEvenPrefix, gubaPrefix]
  omega

/-- Least admissible Q index given a period and a previous weight.
The paper uses r = 10^70, and the common integer scaling of the
lengths cancels from the inequality |Q| > r |C|. -/
noncomputable def chooseEvenPrefixIndex (C : F) (previousWeight : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_gubaEvenPrefix_weight_gt
    (max (10^70 * weightedLength C) previousWeight))

theorem chooseEvenPrefixIndex_spec (C : F) (previousWeight : ℕ) :
    max (10^70 * weightedLength C) previousWeight <
      weightedLength (positiveWord (gubaEvenPrefix (chooseEvenPrefixIndex C previousWeight))) := by
  classical
  exact Nat.find_spec (exists_gubaEvenPrefix_weight_gt
    (max (10^70 * weightedLength C) previousWeight))

theorem chooseEvenPrefixIndex_min (C : F) (previousWeight m : ℕ)
    (hm : max (10^70 * weightedLength C) previousWeight <
      weightedLength (positiveWord (gubaEvenPrefix m))) :
    chooseEvenPrefixIndex C previousWeight ≤ m := by
  classical
  exact Nat.find_min' (exists_gubaEvenPrefix_weight_gt
    (max (10^70 * weightedLength C) previousWeight)) hm

/-- Raw concatenation of the first m positive long blocks. -/
def longRaw (q : List (Fin 2)) : ℕ → List (Fin 2)
  | 0 => []
  | m+1 => longRaw q m ++ longBlock q m

theorem positiveWord_longRaw (q : List (Fin 2)) (m : ℕ) :
    positiveWord (longRaw q m) = longConjugator (positiveWord q) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [longRaw, positiveWord_append, positiveWord_longBlock, ih]
    simp only [longConjugator, List.range_succ, List.map_append,
      List.map_singleton, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

/-- Exact doubled weight, avoiding division in Nat. In particular this
implies the quadratic lower bound used in property 1.9 of the paper. -/
theorem weightedLength_longRaw_twice (q : List (Fin 2)) (m : ℕ) :
    2 * weightedLength (positiveWord (longRaw q m)) =
      6*m*10^80 + m*(m+1)*weightedLength (positiveWord q) := by
  induction m with
  | zero => simp [longRaw, positiveWord, weightedLength, rawWeight]
  | succ m ih =>
    rw [longRaw, positiveWord_append, weightedLength_positive_mul, weightedLength_longBlock]
    rw [Nat.mul_add, ih]
    ring

theorem weightedLength_longConjugator_twice (q : List (Fin 2)) (m : ℕ) :
    2 * weightedLength (longConjugator (positiveWord q) m) =
      6*m*10^80 + m*(m+1)*weightedLength (positiveWord q) := by
  rw [← positiveWord_longRaw]
  exact weightedLength_longRaw_twice q m


/-! ## Resolvent interval estimate (Guba, property 1.9)

The two endpoints of a resolvent are the start of a block and the end
of the following separator. First prove a weighted-coordinate lemma,
then recover actual contiguous subwords using strictly positive weights.
No uniqueness of resolvents, nor graded-diagram claim, is made here.
-/

theorem markerInterval_of_large (S : ℕ → ℕ) (L D h l r : ℕ)
    (hz : S 0 = 0)
    (hs : ∀ j, S (j+1) = S j + D + (j+1)*L)
    (hh : 8 ≤ h) (hD : 2*D ≤ L)
    (hearly : S 7 + D ≤ 2*h*L)
    (hr : r ≤ S h) (hlong : l + 2*h*L < r) :
    ∃ k, 7 ≤ k ∧ k < h ∧ l ≤ S (k-1) ∧ S k + D ≤ r := by
  classical
  have hmono : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hs]
    omega
  have hex : ∃ j, l < S j := ⟨h, by omega⟩
  let j := Nat.find hex
  have hj : l < S j := Nat.find_spec hex
  have hjh : j ≤ h := Nat.find_min' hex (by omega)
  have hjpos : 0 < j := by
    by_contra hn
    have he : j = 0 := by omega
    rw [he, hz] at hj
    omega
  have hjprev : S (j-1) ≤ l := by
    by_contra hn
    have hlt : l < S (j-1) := by omega
    have hm : j ≤ j-1 := Nat.find_min' hex hlt
    omega
  by_cases hsmall : j ≤ 6
  · refine ⟨7, by omega, by omega, ?_, by omega⟩
    have hm := hmono hsmall
    change l ≤ S 6
    omega
  · by_cases hmid : j+1 < h
    · refine ⟨j+1, by omega, hmid, ?_, ?_⟩
      · have he : j+1-1 = j := by omega
        rw [he]
        exact le_of_lt hj
      · have hej : j-1+1 = j := by omega
        have hsj := hs (j-1)
        rw [hej] at hsj
        have hsj1 := hs j
        have hm1 : (j+2)*L ≤ h*L :=
          Nat.mul_le_mul_right L (by omega)
        have hm2 : (j+1)*L ≤ h*L :=
          Nat.mul_le_mul_right L (by omega)
        have he1 : (j+2)*L = j*L+2*L := by ring
        have he2 : 2*h*L = h*L+h*L := by ring
        omega
    · have hidx : h-2 ≤ j-1 := by omega
      have hm := hmono hidx
      have he1 : h-2+1 = h-1 := by omega
      have he2 : h-1+1 = h := by omega
      have hstep1 := hs (h-2)
      have hstep2 := hs (h-1)
      rw [he1] at hstep1
      rw [he2] at hstep2
      have hm1 : (h-1)*L+L = h*L := by
        calc
          _ = (h-1+1)*L := by ring
          _ = _ := by rw [he2]
      have hm2 : 2*h*L = h*L+h*L := by ring
      omega

abbrev positiveWeight (q : List (Fin 2)) : ℕ :=
  weightedLength (positiveWord q)

theorem positiveWeight_append (p q : List (Fin 2)) :
    positiveWeight (p ++ q) = positiveWeight p + positiveWeight q := by
  change weightedLength (positiveWord (p ++ q)) =
    weightedLength (positiveWord p) + weightedLength (positiveWord q)
  rw [positiveWord_append, weightedLength_positive_mul]

theorem positiveWeight_nil : positiveWeight [] = 0 := by
  change weightedLength (positiveWord []) = 0
  rw [weightedLength, toWord_positiveWord]
  rfl

theorem positiveWeight_zero_imp_nil (q : List (Fin 2))
    (hq : positiveWeight q = 0) : q = [] := by
  have hl : q.length ≤ positiveWeight q := positiveWord_length_le q
  have hz : q.length = 0 := by omega
  exact List.length_eq_zero_iff.mp hz

/-- For two prefixes of the same word, their weighted lengths determine
their inclusion order; no assumption of equal letter weights is used. -/
theorem prefix_of_positiveWeight_le {p q x : List (Fin 2)}
    (hp : p <+: x) (hq : q <+: x)
    (h : positiveWeight p ≤ positiveWeight q) : p <+: q := by
  rcases List.prefix_or_prefix_of_prefix hp hq with hpre | hpre
  · exact hpre
  · obtain ⟨t, ht⟩ := List.prefix_iff_exists_append_eq.mp hpre
    have hsum := congrArg positiveWeight ht
    rw [positiveWeight_append] at hsum
    have hzero : positiveWeight t = 0 := by omega
    have hnil := positiveWeight_zero_imp_nil t hzero
    subst t
    simp only [List.append_nil] at ht
    subst p
    exact List.prefix_rfl

/-- Inclusion of weighted intervals of a single word implies literal
contiguous factor containment. -/
theorem factor_of_weighted_interval
    (p z r u m v : List (Fin 2))
    (heq : p ++ z ++ r = u ++ m ++ v)
    (hstart : positiveWeight p ≤ positiveWeight u)
    (hend : positiveWeight (u ++ m) ≤ positiveWeight (p ++ z)) :
    ∃ left right, z = left ++ m ++ right := by
  have hp : p <+: p ++ z ++ r := by
    rw [List.append_assoc]
    exact List.prefix_append _ _
  have hu : u <+: p ++ z ++ r := by
    rw [heq, List.append_assoc]
    exact List.prefix_append _ _
  have hum : u ++ m <+: p ++ z ++ r := by
    rw [heq]
    exact List.prefix_append _ _
  have hpz : p ++ z <+: p ++ z ++ r := List.prefix_append _ _
  obtain ⟨left, hl⟩ := List.prefix_iff_exists_append_eq.mp
    (prefix_of_positiveWeight_le hp hu hstart)
  obtain ⟨right, hh⟩ := List.prefix_iff_exists_append_eq.mp
    (prefix_of_positiveWeight_le hum hpz hend)
  refine ⟨left, right, ?_⟩
  have hc : p ++ z = p ++ (left ++ m ++ right) := by
    rw [← hh, ← hl]
    simp only [List.append_assoc]
  exact List.append_inj_right hc rfl

theorem longRaw_prefix (q : List (Fin 2)) {i j : ℕ} (hij : i ≤ j) :
    longRaw q i <+: longRaw q j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction n with
  | zero => simp
  | succ n ih =>
    exact (ih (by omega)).trans (List.prefix_append _ _)

def resolventRaw (q : List (Fin 2)) (k : ℕ) : List (Fin 2) :=
  longBlock q (k-1) ++ List.replicate 3 1

/-- The prescribed separator-power-separator factor occurs at the
start of its kth block, as a literal list factor. -/
theorem longRaw_resolvent_factor (q : List (Fin 2)) (k h : ℕ)
    (hk : 0 < k) (hkh : k < h) :
    ∃ v, longRaw q h = longRaw q (k-1) ++ resolventRaw q k ++ v := by
  obtain ⟨t, ht⟩ := List.prefix_iff_exists_append_eq.mp
    (longRaw_prefix q (show k+1 ≤ h by omega))
  have hrec : longRaw q k = longRaw q (k-1) ++ longBlock q (k-1) := by
    have he : k-1+1 = k := by omega
    calc
      longRaw q k = longRaw q (k-1+1) := congrArg (longRaw q) he.symm
      _ = _ := rfl
  refine ⟨(List.replicate (k+1) q).flatten ++ t, ?_⟩
  rw [← ht]
  change (longRaw q k ++ longBlock q k) ++ t = _
  rw [hrec, resolventRaw]
  simp only [longBlock, List.append_assoc]

theorem positiveWeight_separator :
    positiveWeight (List.replicate 3 (1 : Fin 2)) = 3*10^80 := by
  change weightedLength (positiveWord (List.replicate 3 (1 : Fin 2))) = 3*10^80
  rw [weightedLength, toWord_positiveWord]
  norm_num [rawWeight, letterWeight]

theorem positiveWeight_resolvent_end (q : List (Fin 2)) (k : ℕ)
    (hk : 0 < k) :
    positiveWeight (longRaw q (k-1) ++ resolventRaw q k) =
      positiveWeight (longRaw q k) + 3*10^80 := by
  have hrec : longRaw q k = longRaw q (k-1) ++ longBlock q (k-1) := by
    have he : k-1+1 = k := by omega
    calc
      longRaw q k = longRaw q (k-1+1) := congrArg (longRaw q) he.symm
      _ = _ := rfl
  rw [hrec, resolventRaw, ← List.append_assoc, positiveWeight_append,
    positiveWeight_separator]

/-- Integral version of the numerical comparison in property 1.9,
with h = 10^20, epsilon = 1/120, beta = 10^-17. -/
theorem guba19_threshold (q : List (Fin 2)) :
    240*10^17 * (2*10^20 * positiveWeight q) <
      positiveWeight (longRaw q (10^20)) := by
  have he := weightedLength_longRaw_twice q (10^20)
  change 2 * positiveWeight (longRaw q (10^20)) =
    6*10^20*10^80 + 10^20*(10^20+1)*positiveWeight q at he
  norm_num at he ⊢
  omega

/-- Property 1.9, in the positive raw-word model and with an explicit
lower bound on Q's weight. The latter must still be discharged for the
rank-indexed choice of Q in the original construction. -/
theorem guba19_resolvent (q p z r : List (Fin 2))
    (hq : 6*10^80 ≤ positiveWeight q)
    (hword : longRaw q (10^20) = p ++ z ++ r)
    (hlong : positiveWeight (longRaw q (10^20)) <
      240*10^17 * positiveWeight z) :
    ∃ k, 7 ≤ k ∧ k < 10^20 ∧
      ∃ left right, z = left ++ resolventRaw q k ++ right := by
  have hthr := guba19_threshold q
  have hlarge : 2*10^20 * positiveWeight q < positiveWeight z := by
    by_contra hn
    have hm := Nat.mul_le_mul_left (240*10^17)
      (show positiveWeight z ≤ 2*10^20 * positiveWeight q by omega)
    omega
  have hzero : positiveWeight (longRaw q 0) = 0 := positiveWeight_nil
  have hstep (j : ℕ) : positiveWeight (longRaw q (j+1)) =
      positiveWeight (longRaw q j) + 3*10^80 + (j+1)*positiveWeight q := by
    rw [longRaw, positiveWeight_append]
    have hb := weightedLength_longBlock q j
    change positiveWeight (longBlock q j) = 3*10^80 + (j+1)*positiveWeight q at hb
    rw [hb, Nat.add_assoc]
  have hearly : positiveWeight (longRaw q 7) + 3*10^80 ≤
      2*10^20 * positiveWeight q := by
    have he := weightedLength_longRaw_twice q 7
    change 2*positiveWeight (longRaw q 7) =
      6*7*10^80 + 7*(7+1)*positiveWeight q at he
    norm_num at he hq ⊢
    omega
  have hright : positiveWeight (p ++ z) ≤ positiveWeight (longRaw q (10^20)) := by
    rw [hword, positiveWeight_append (p ++ z) r]
    exact Nat.le_add_right _ _
  have hlong' : positiveWeight p + 2*10^20*positiveWeight q <
      positiveWeight (p ++ z) := by
    rw [positiveWeight_append]
    omega
  obtain ⟨k, hk, hkh, hstart, hend⟩ :=
    markerInterval_of_large (fun n => positiveWeight (longRaw q n))
      (positiveWeight q) (3*10^80) (10^20) (positiveWeight p)
      (positiveWeight (p ++ z)) hzero hstep (by norm_num)
      (by norm_num at hq ⊢; omega) hearly hright hlong'
  obtain ⟨v, hv⟩ := longRaw_resolvent_factor q k (10^20) (by omega) hkh
  have heq : p ++ z ++ r = longRaw q (k-1) ++ resolventRaw q k ++ v :=
    hword.symm.trans hv
  have hend' : positiveWeight (longRaw q (k-1) ++ resolventRaw q k) ≤
      positiveWeight (p ++ z) := by
    rw [positiveWeight_resolvent_end q k (by omega)]
    exact hend
  exact ⟨k, hk, hkh, factor_of_weighted_interval p z r _ _ v heq hstart hend'⟩


/-! ## Discharging the weight hypothesis in property 1.9

A bad word necessarily uses the expensive generator. Thus the
paper's inequality |Q| > 10^70 |C| already implies the lower bound
on |Q| used in guba19_resolvent. No geometric assumption is needed.
-/

/-- A raw word weighing less than one b-letter consists entirely of
signed a-letters, and therefore represents an integral power of a. -/
theorem mk_eq_a_zpow_of_light (w : RawWord) (hw : rawWeight w < 10^80) :
    ∃ n : ℤ, FreeGroup.mk w = a ^ n := by
  induction w with
  | nil => exact ⟨0, by rw [zpow_zero, FreeGroup.one_eq_mk]⟩
  | cons x xs ih =>
    have hw' : letterWeight x + rawWeight xs < 10^80 := hw
    have hx : x.1 = 0 := by
      by_contra hne
      have hlarge : letterWeight x = 10^80 := by simp [letterWeight, hne]
      omega
    obtain ⟨n, hn⟩ := ih (by omega)
    rcases x with ⟨i, s⟩
    change i = 0 at hx
    subst i
    have hmul : FreeGroup.mk ((0,s)::xs) =
        FreeGroup.mk [(0,s)] * FreeGroup.mk xs := by
      exact (FreeGroup.mul_mk (L₁ := [(0,s)]) (L₂ := xs)).symm
    cases s with
    | false =>
      refine ⟨-1+n, ?_⟩
      rw [hmul, FreeGroup.mk_eq_inv_of, hn, zpow_add]
      simp [a]
    | true =>
      refine ⟨1+n, ?_⟩
      rw [hmul, FreeGroup.mk_eq_of, hn, zpow_add]
      simp [a]

theorem eq_a_zpow_of_light (w : F) (hw : weightedLength w < 10^80) :
    ∃ n : ℤ, w = a ^ n := by
  obtain ⟨n, hn⟩ := mk_eq_a_zpow_of_light w.toWord hw
  rw [FreeGroup.mk_toWord] at hn
  exact ⟨n, hn⟩

theorem good_a_zpow (N : Subgroup F) (n : ℤ) : Good N (a ^ n) := by
  refine ⟨1, n, ?_⟩
  simp

/-- Every bad period has weight at least the weight of b. -/
theorem weight_ge_of_bad (N : Subgroup F) (C : F) (hbad : ¬ Good N C) :
    10^80 ≤ weightedLength C := by
  by_contra! h
  obtain ⟨n, hn⟩ := eq_a_zpow_of_light C h
  apply hbad
  rw [hn]
  exact good_a_zpow N n

theorem chosenEvenPrefix_weight_ge (N : Subgroup F) (C : F)
    (hbad : ¬ Good N C) (previousWeight : ℕ) :
    6*10^80 ≤ positiveWeight (gubaEvenPrefix (chooseEvenPrefixIndex C previousWeight)) := by
  have h := chooseEvenPrefixIndex_spec C previousWeight
  have hlt := lt_of_le_of_lt
    (le_max_left (10^70 * weightedLength C) previousWeight) h
  calc
    6*10^80 ≤ (10^70 : ℕ)*10^80 := by norm_num
    _ ≤ 10^70*weightedLength C :=
      Nat.mul_le_mul_left _ (weight_ge_of_bad N C hbad)
    _ ≤ _ := le_of_lt hlt

/-- Property 1.9 specialized to the actual least-index prefix choice.
The auxiliary weight bound is now a consequence, not an extra
hypothesis. The geometry and uniqueness of resolvents remain open. -/
theorem guba19_chosen_resolvent (N : Subgroup F) (C : F)
    (hbad : ¬ Good N C) (previousWeight : ℕ) (p z r : List (Fin 2)) :
    let q := gubaEvenPrefix (chooseEvenPrefixIndex C previousWeight)
    longRaw q (10^20) = p ++ z ++ r →
    positiveWeight (longRaw q (10^20)) < 240*10^17 * positiveWeight z →
    ∃ k, 7 ≤ k ∧ k < 10^20 ∧
      ∃ left right, z = left ++ resolventRaw q k ++ right := by
  dsimp only
  intro hword hlong
  exact guba19_resolvent _ p z r
    (chosenEvenPrefix_weight_ge N C hbad previousWeight) hword hlong


/-! ## Periodic factors of the special prefixes

Mathlib's Fine–Wilf theorem uses ordinary letter count, not Guba's
weighted metric. Connect its period predicate to the cube-free
Thue–Morse prefix proved above. These are local word bounds, not
yet the full resolvent-uniqueness or overlap estimates of the paper.
-/

/-- A factor of a Thue–Morse prefix with positive period d contains
strictly fewer than three full periods. -/
theorem thueFactor_period_bound (n d : ℕ) (p v r : List (Fin 2))
    (hword : thuePrefix n = p ++ v ++ r)
    (hd : 0 < d) (hperiod : v.HasPeriod d) :
    v.length < 3*d := by
  by_contra! hlong
  have hlen := congrArg List.length hword
  simp only [thuePrefix_length, List.length_append] at hlen
  have hshift (j : ℕ) (hj : j < v.length) :
      (thuePrefix n)[p.length+j]? = v[j]? := by
    rw [hword, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    rw [show p.length+j-p.length = j by omega]
  apply thuePrefix_cubeFree n p.length d hd (by omega)
  intro j hj
  have hper := List.hasPeriod_iff_getElem?.mp hperiod j (by omega)
  have heq : (thuePrefix n)[p.length+j]? = (thuePrefix n)[p.length+j+d]? := by
    rw [hshift j (by omega), show p.length+j+d = p.length+(j+d) by omega,
      hshift (j+d) (by omega)]
    exact hper
  rw [getElem?_pos (thuePrefix n) (p.length+j) (by rw [thuePrefix_length]; omega),
    getElem?_pos (thuePrefix n) (p.length+j+d) (by rw [thuePrefix_length]; omega)] at heq
  exact Option.some.inj heq

/-- If two periods of such a factor satisfy the Fine–Wilf threshold,
the cube-free bound applies to their gcd. -/
theorem thueFactor_twoPeriods_bound (n d e : ℕ) (p v r : List (Fin 2))
    (hword : thuePrefix n = p ++ v ++ r)
    (hd : 0 < d.gcd e)
    (hp : v.HasPeriod d) (hq : v.HasPeriod e)
    (hfit : d+e-d.gcd e ≤ v.length) :
    v.length < 3*(d.gcd e) :=
  thueFactor_period_bound n (d.gcd e) p v r hword hd (hp.gcd hq hfit)

/-- In particular the same bound holds for the selected even-indexed
prefixes used to construct the long conjugating words. -/
theorem gubaEvenPrefix_period_bound (m d : ℕ) (hd : 0 < d)
    (hperiod : (gubaEvenPrefix m).HasPeriod d) :
    (gubaEvenPrefix m).length < 3*d := by
  apply thueFactor_period_bound (prefixEnd (2*m+1)+1) d [] (gubaEvenPrefix m) []
  · simp [gubaEvenPrefix, gubaPrefix]
  · exact hd
  · exact hperiod


/-! ## Literal separator positions

A marker is exactly three consecutive occurrences of the long generator.
The following lemmas use the actual list positions, not group equality.
A zero letter at either end of a seam prevents a marker crossing it.
-/

def TripleBAt (w : List (Fin 2)) (i : ℕ) : Prop :=
  w[i]? = some 1 ∧ w[i+1]? = some 1 ∧ w[i+2]? = some 1

theorem tripleBAt_fits {w : List (Fin 2)} {i : ℕ}
    (h : TripleBAt w i) : i+3 ≤ w.length := by
  obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp h.2.2
  omega

theorem tripleBAt_letter {w : List (Fin 2)} {i j : ℕ}
    (h : TripleBAt w i) (hlo : i ≤ j) (hhi : j ≤ i+2) :
    w[j]? = some 1 := by
  have hj : j = i ∨ j = i+1 ∨ j = i+2 := by omega
  rcases hj with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem tripleBAt_append_left (u v : List (Fin 2)) (i : ℕ)
    (hfit : i+3 ≤ u.length) :
    TripleBAt (u++v) i ↔ TripleBAt u i := by
  unfold TripleBAt
  rw [List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]

theorem tripleBAt_append_right (u v : List (Fin 2)) (i : ℕ)
    (hi : u.length ≤ i) :
    TripleBAt (u++v) i ↔ TripleBAt v (i-u.length) := by
  unfold TripleBAt
  rw [List.getElem?_append_right hi,
      List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
  rw [show i+1-u.length = i-u.length+1 by omega,
      show i+2-u.length = i-u.length+2 by omega]

/-- No occurrence of bbb can cross a seam protected by a zero letter. -/
theorem tripleBAt_no_cross (u v : List (Fin 2)) (i : ℕ)
    (hi : i < u.length) (hc : u.length ≤ i+2)
    (hguard : u[u.length-1]? = some 0 ∨ v[0]? = some 0) :
    ¬ TripleBAt (u++v) i := by
  intro ht
  rcases hguard with hu | hv
  · have h := tripleBAt_letter ht (show i ≤ u.length-1 by omega)
      (show u.length-1 ≤ i+2 by omega)
    rw [List.getElem?_append_left (by omega), hu] at h
    simp at h
  · have h := tripleBAt_letter ht (show i ≤ u.length by omega) hc
    rw [List.getElem?_append_right (by omega), Nat.sub_self, hv] at h
    simp at h

/-- Exhaustive location of a marker in a concatenation with protected seam. -/
theorem tripleBAt_guarded_append (u v : List (Fin 2)) (i : ℕ)
    (hguard : u[u.length-1]? = some 0 ∨ v[0]? = some 0) :
    TripleBAt (u++v) i ↔
      (i+3 ≤ u.length ∧ TripleBAt u i) ∨
      (u.length ≤ i ∧ TripleBAt v (i-u.length)) := by
  constructor
  · intro ht
    by_cases hi : u.length ≤ i
    · exact Or.inr ⟨hi, (tripleBAt_append_right u v i hi).mp ht⟩
    · by_cases hf : i+3 ≤ u.length
      · exact Or.inl ⟨hf, (tripleBAt_append_left u v i hf).mp ht⟩
      · exact False.elim (tripleBAt_no_cross u v i (by omega) (by omega) hguard ht)
  · rintro (⟨hf,ht⟩ | ⟨hi,ht⟩)
    · exact (tripleBAt_append_left u v i hf).mpr ht
    · exact (tripleBAt_append_right u v i hi).mpr ht

/-- Cube-freeness rules out bbb at every position of a Thue–Morse prefix. -/
theorem thuePrefix_no_tripleB (n i : ℕ) :
    ¬ TripleBAt (thuePrefix n) i := by
  intro ht
  have hf := tripleBAt_fits ht
  rw [thuePrefix_length] at hf
  apply thuePrefix_cubeFree n i 1 (by omega) (by omega)
  intro j hj
  have h1 := tripleBAt_letter ht (show i ≤ i+j by omega)
    (show i+j ≤ i+2 by omega)
  have h2 := tripleBAt_letter ht (show i ≤ i+j+1 by omega)
    (show i+j+1 ≤ i+2 by omega)
  rw [getElem?_pos (thuePrefix n) (i+j) (by rw [thuePrefix_length]; omega)] at h1
  rw [getElem?_pos (thuePrefix n) (i+j+1) (by rw [thuePrefix_length]; omega)] at h2
  exact (Option.some.inj h1).trans (Option.some.inj h2).symm

theorem gubaPrefix_no_tripleB (m i : ℕ) :
    ¬ TripleBAt (gubaPrefix m) i :=
  thuePrefix_no_tripleB (prefixEnd m+1) i

theorem gubaPrefix_head_zero (m : ℕ) :
    (gubaPrefix m)[0]? = some 0 := by
  rw [getElem?_pos (gubaPrefix m) 0 (by rw [gubaPrefix, thuePrefix_length]; omega)]
  exact congrArg some (gubaPrefix_first m)

theorem gubaPrefix_last_zero (m : ℕ) :
    (gubaPrefix m)[(gubaPrefix m).length-1]? = some 0 := by
  have he : (gubaPrefix m).length-1 = prefixEnd m := by
    rw [gubaPrefix, thuePrefix_length]
    omega
  rw [he, getElem?_pos (gubaPrefix m) (prefixEnd m) (by rw [gubaPrefix, thuePrefix_length]; omega)]
  exact congrArg some (gubaPrefix_last m)

/-- Repeated copies of a word with a protected last letter introduce
no new bbb occurrences, even across the joins of copies. -/
theorem repeat_no_tripleB (q : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i)
    (hlast : q[q.length-1]? = some 0) (n i : ℕ) :
    ¬ TripleBAt (List.replicate n q).flatten i := by
  induction n generalizing i with
  | zero =>
    intro ht
    have hf := tripleBAt_fits ht
    simp at hf
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    intro ht
    rcases (tripleBAt_guarded_append q (List.replicate n q).flatten i
      (Or.inl hlast)).mp ht with h | h
    · exact hq i h.2
    · exact ih (i-q.length) h.2

theorem repeat_head_zero (q : List (Fin 2)) (hq : q[0]? = some 0)
    (n : ℕ) :
    (List.replicate (n+1) q).flatten[0]? = some 0 := by
  have hlen : 0 < q.length := (List.getElem?_eq_some_iff.mp hq).choose
  rw [List.replicate_succ, List.flatten_cons, List.getElem?_append_left hlen]
  exact hq

theorem repeat_last_zero (q : List (Fin 2))
    (hq : q[q.length-1]? = some 0) (n : ℕ) :
    (List.replicate (n+1) q).flatten[
      (List.replicate (n+1) q).flatten.length-1]? = some 0 := by
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hq
  have hpos : 0 < q.length := by omega
  rw [List.replicate_succ', List.flatten_concat]
  rw [List.length_append, List.getElem?_append_right (by omega)]
  rw [show (List.replicate n q).flatten.length+q.length-1-
    (List.replicate n q).flatten.length = q.length-1 by omega]
  exact hq

/-- The literal separator bbb has exactly one marker position. -/
theorem separator_tripleB_iff (i : ℕ) :
    TripleBAt (List.replicate 3 (1 : Fin 2)) i ↔ i = 0 := by
  constructor
  · intro h
    have hf := tripleBAt_fits h
    simp at hf
    omega
  · rintro rfl
    unfold TripleBAt
    decide

/-- Inside each long block bbb Q^(j+1), the only bbb starts at zero. -/
theorem longBlock_tripleB_iff (q : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i) (hhead : q[0]? = some 0)
    (hlast : q[q.length-1]? = some 0) (j i : ℕ) :
    TripleBAt (longBlock q j) i ↔ i = 0 := by
  unfold longBlock
  rw [tripleBAt_guarded_append _ _ i (Or.inr (repeat_head_zero q hhead j))]
  constructor
  · rintro (⟨_,h⟩ | ⟨_,h⟩)
    · exact (separator_tripleB_iff i).mp h
    · exact False.elim (repeat_no_tripleB q hq hlast (j+1) _ h)
  · rintro rfl
    exact Or.inl ⟨by decide, (separator_tripleB_iff 0).mpr rfl⟩

theorem longBlock_last_zero (q : List (Fin 2))
    (hlast : q[q.length-1]? = some 0) (j : ℕ) :
    (longBlock q j)[(longBlock q j).length-1]? = some 0 := by
  have h := repeat_last_zero q hlast j
  obtain ⟨hp, _⟩ := List.getElem?_eq_some_iff.mp h
  unfold longBlock
  rw [List.length_append, List.getElem?_append_right (by omega)]
  rw [show (List.replicate 3 (1 : Fin 2)).length +
    (List.replicate (j+1) q).flatten.length-1-
    (List.replicate 3 (1 : Fin 2)).length =
    (List.replicate (j+1) q).flatten.length-1 by omega]
  exact h

theorem longRaw_last_zero (q : List (Fin 2))
    (hlast : q[q.length-1]? = some 0) (h : ℕ) :
    (longRaw q (h+1))[(longRaw q (h+1)).length-1]? = some 0 := by
  have hb := longBlock_last_zero q hlast h
  obtain ⟨hp, _⟩ := List.getElem?_eq_some_iff.mp hb
  rw [longRaw, List.length_append, List.getElem?_append_right (by omega)]
  rw [show (longRaw q h).length + (longBlock q h).length-1-
    (longRaw q h).length = (longBlock q h).length-1 by omega]
  exact hb

/-- The markers in the full conjugator are exactly the starts of its
indexed blocks. This does not yet establish cross-rank resolvent uniqueness. -/
theorem longRaw_tripleB_iff (q : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i) (hhead : q[0]? = some 0)
    (hlast : q[q.length-1]? = some 0) (h i : ℕ) :
    TripleBAt (longRaw q h) i ↔ ∃ j < h, i = (longRaw q j).length := by
  induction h generalizing i with
  | zero => simp [longRaw, TripleBAt]
  | succ h ih =>
    cases h with
    | zero =>
      simpa [longRaw] using longBlock_tripleB_iff q hq hhead hlast 0 i
    | succ h =>
      rw [longRaw, tripleBAt_guarded_append _ _ i
        (Or.inl (longRaw_last_zero q hlast h))]
      constructor
      · rintro (⟨_,ht⟩ | ⟨hi,ht⟩)
        · obtain ⟨j,hj,he⟩ := (ih i).mp ht
          exact ⟨j, by omega, he⟩
        · have he := (longBlock_tripleB_iff q hq hhead hlast (h+1) _).mp ht
          exact ⟨h+1, by omega, by omega⟩
      · rintro ⟨j,hj,he⟩
        by_cases hlastIndex : j = h+1
        · subst j
          exact Or.inr ⟨by omega, (longBlock_tripleB_iff q hq hhead hlast _ _).mpr (by omega)⟩
        · have hj' : j < h+1 := by omega
          have ht := (ih i).mpr ⟨j,hj',he⟩
          exact Or.inl ⟨tripleBAt_fits ht, ht⟩

theorem gubaEvenPrefix_longRaw_tripleB_iff (m h i : ℕ) :
    TripleBAt (longRaw (gubaEvenPrefix m) h) i ↔
      ∃ j < h, i = (longRaw (gubaEvenPrefix m) j).length :=
  longRaw_tripleB_iff (gubaEvenPrefix m)
    (gubaPrefix_no_tripleB (2*m+1)) (gubaPrefix_head_zero (2*m+1))
    (gubaPrefix_last_zero (2*m+1)) h i


/-! ## Complete resolvent positions

A complete resolvent has two markers, with none in its interior.
Matching a resolvent inside another long word must therefore match
two consecutive block starts. This fixes the source position in
the same-rank case and gives the exact intervening power length
for the cross-rank case.
-/

theorem repeated_length (q : List (Fin 2)) (k : ℕ) :
    (List.replicate k q).flatten.length = k*q.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append,
      ih, Nat.succ_mul, Nat.add_comm]

theorem longBlock_length (q : List (Fin 2)) (j : ℕ) :
    (longBlock q j).length = 3+(j+1)*q.length := by
  simp [longBlock, repeated_length]

theorem longRaw_length_step (q : List (Fin 2)) (j : ℕ) :
    (longRaw q (j+1)).length = (longRaw q j).length + (3+(j+1)*q.length) := by
  rw [longRaw, List.length_append, longBlock_length]

theorem longRaw_length_strictMono (q : List (Fin 2)) :
    StrictMono (fun j => (longRaw q j).length) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [longRaw_length_step]
  omega

theorem tripleBAt_factor_iff (p v s : List (Fin 2)) (i : ℕ)
    (hfit : i+3 ≤ v.length) :
    TripleBAt (p++v++s) (p.length+i) ↔ TripleBAt v i := by
  have hf : p.length+i+3 ≤ (p++v).length := by
    simp only [List.length_append]
    omega
  rw [tripleBAt_append_left (p++v) s _ hf,
      tripleBAt_append_right p v _ (by omega), Nat.add_sub_cancel_left]

theorem resolvent_tripleB_iff (q : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i) (hhead : q[0]? = some 0)
    (hlast : q[q.length-1]? = some 0) (k i : ℕ) :
    TripleBAt (resolventRaw q k) i ↔
      i = 0 ∨ i = (longBlock q (k-1)).length := by
  unfold resolventRaw
  rw [tripleBAt_guarded_append _ _ i (Or.inl (longBlock_last_zero q hlast (k-1)))]
  rw [longBlock_tripleB_iff q hq hhead hlast, separator_tripleB_iff]
  have hlen := longBlock_length q (k-1)
  omega

/-- The marker positions of a complete resolvent must be consecutive
marker positions of the containing long word. -/
theorem resolvent_occurrence_gap (q v p s : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i) (hqh : q[0]? = some 0)
    (hql : q[q.length-1]? = some 0)
    (hv : ∀ i, ¬ TripleBAt v i) (hvh : v[0]? = some 0)
    (hvl : v[v.length-1]? = some 0)
    (h k : ℕ) (hk : 0 < k)
    (heq : longRaw q h = p ++ resolventRaw v k ++ s) :
    ∃ j, j+1 < h ∧ p.length = (longRaw q j).length ∧
      (j+1)*q.length = k*v.length := by
  let L := (longBlock v (k-1)).length
  have hL : L = 3+k*v.length := by
    dsimp [L]
    rw [longBlock_length, show k-1+1 = k by omega]
  have hrlen : (resolventRaw v k).length = L+3 := by
    simp [resolventRaw, L]
  have hstart : TripleBAt (longRaw q h) p.length := by
    rw [heq, show p.length = p.length+0 by omega]
    apply (tripleBAt_factor_iff p (resolventRaw v k) s 0 (by omega)).mpr
    exact (resolvent_tripleB_iff v hv hvh hvl k 0).mpr (Or.inl rfl)
  have hend : TripleBAt (longRaw q h) (p.length+L) := by
    rw [heq]
    apply (tripleBAt_factor_iff p (resolventRaw v k) s L (by omega)).mpr
    exact (resolvent_tripleB_iff v hv hvh hvl k L).mpr (Or.inr rfl)
  obtain ⟨j,hj,hjpos⟩ := (longRaw_tripleB_iff q hq hqh hql h _).mp hstart
  obtain ⟨t,ht,htpos⟩ := (longRaw_tripleB_iff q hq hqh hql h _).mp hend
  have hmono := longRaw_length_strictMono q
  have hjt : j < t := by
    apply hmono.lt_iff_lt.mp
    omega
  have hconsecutive : t = j+1 := by
    by_contra hne
    have hlt : j+1 < t := by omega
    have hmidL := hmono (Nat.lt_succ_self j)
    have hmidR := hmono hlt
    let i := (longRaw q (j+1)).length-p.length
    have hi : p.length+i = (longRaw q (j+1)).length := by dsimp [i]; omega
    have hip : 0 < i := by dsimp [i]; omega
    have hil : i < L := by dsimp [i]; omega
    have hm : TripleBAt (longRaw q h) (p.length+i) :=
      (longRaw_tripleB_iff q hq hqh hql h _).mpr ⟨j+1, by omega, hi⟩
    rw [heq] at hm
    have hm' := (tripleBAt_factor_iff p (resolventRaw v k) s i (by omega)).mp hm
    have hc := (resolvent_tripleB_iff v hv hvh hvl k i).mp hm'
    change i = 0 ∨ i = L at hc
    omega
  subst t
  have hstep := longRaw_length_step q j
  exact ⟨j,ht,hjpos,by omega⟩

/-- For a fixed prefix Q, every occurrence of its kth resolvent starts
at the kth block, and the following block exists. -/
theorem samePrefix_resolvent_position (q p s : List (Fin 2))
    (hq : ∀ i, ¬ TripleBAt q i) (hhead : q[0]? = some 0)
    (hlast : q[q.length-1]? = some 0) (h k : ℕ) (hk : 0 < k)
    (heq : longRaw q h = p ++ resolventRaw q k ++ s) :
    k < h ∧ p.length = (longRaw q (k-1)).length := by
  obtain ⟨j,hj,hpos,hgap⟩ := resolvent_occurrence_gap q q p s
    hq hhead hlast hq hhead hlast h k hk heq
  have hqpos : 0 < q.length := (List.getElem?_eq_some_iff.mp hhead).choose
  have hidx := Nat.mul_right_cancel hqpos hgap
  have hsub : k-1 = j := by omega
  rw [hsub]
  exact ⟨by omega,hpos⟩


/-! ## Recovering the selected prefix from a positive power

An odd-length cube-free prefix has no proper positive period dividing
its length. Fine–Wilf then identifies two such prefixes when their
positive powers agree. All lengths in this section count letters.
-/

theorem gubaEvenPrefix_odd_length (m : ℕ) :
    (gubaEvenPrefix m).length % 2 = 1 :=
  gubaPrefix_odd_length (2*m+1)

theorem gubaEvenPrefix_dividing_period (m d : ℕ)
    (hd : 0 < d) (hper : (gubaEvenPrefix m).HasPeriod d)
    (hdvd : d ∣ (gubaEvenPrefix m).length) :
    d = (gubaEvenPrefix m).length := by
  have hb := gubaEvenPrefix_period_bound m d hd hper
  have ho := gubaEvenPrefix_odd_length m
  obtain ⟨k,hk⟩ := hdvd
  have hklt : k < 3 := by
    by_contra! hh
    have hmul := Nat.mul_le_mul_left d hh
    rw [← hk] at hmul
    omega
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hk
    omega
  · simpa using hk.symm
  · rw [hk, Nat.mul_comm d 2] at ho
    omega

theorem repeat_take_base (q : List (Fin 2)) (k : ℕ) :
    ((List.replicate (k+1) q).flatten).take q.length = q := by
  rw [List.replicate_succ, List.flatten_cons, List.take_append_length]

theorem repeat_hasPeriod (q : List (Fin 2)) (k : ℕ) :
    ((List.replicate k q).flatten).HasPeriod q.length := by
  cases k with
  | zero => simp
  | succ k =>
    rw [List.HasPeriod, repeat_take_base]
    apply List.prefix_iff_exists_append_eq.mpr
    refine ⟨q, ?_⟩
    symm
    calc
      q ++ (List.replicate (k+1) q).flatten =
          (List.replicate ((k+1)+1) q).flatten := by
            rw [List.replicate_succ, List.flatten_cons]
      _ = (List.replicate (k+1) q).flatten ++ q := by
            rw [List.replicate_succ', List.flatten_concat]

theorem repeat_base_infix (q : List (Fin 2)) (k : ℕ) (hk : 0 < k) :
    q <:+: (List.replicate k q).flatten := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  refine ⟨[], (List.replicate t q).flatten, ?_⟩
  simp [List.replicate_succ]

/-- The Fine–Wilf threshold is automatic for a nonempty common power.
If one exponent is one, its length is a multiple of the other base
length; otherwise both base lengths are at most half the total. -/
theorem commonPower_fineWilf_threshold (p q k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (heq : k*p = l*q) :
    p+q-p.gcd q ≤ k*p := by
  by_cases h1 : k = 1
  · subst k
    simp only [one_mul] at heq ⊢
    have hd : q ∣ p := ⟨l, by simpa [Nat.mul_comm] using heq⟩
    rw [Nat.gcd_eq_right hd]
    omega
  · by_cases h2 : l = 1
    · subst l
      simp only [one_mul] at heq
      have hd : p ∣ q := ⟨k, by simpa [Nat.mul_comm] using heq.symm⟩
      rw [Nat.gcd_eq_left hd]
      omega
    · have hp := Nat.mul_le_mul_right p (show 2 ≤ k by omega)
      have hq := Nat.mul_le_mul_right q (show 2 ≤ l by omega)
      omega

/-- Equality of positive powers determines both selected prefix words
and their exponents. The proof uses the existing Mathlib Fine–Wilf
theorem, not a new periodicity theorem. -/
theorem gubaEvenPrefix_commonPower (m n k l : ℕ)
    (hk : 0 < k) (hl : 0 < l)
    (heq : (List.replicate k (gubaEvenPrefix m)).flatten =
      (List.replicate l (gubaEvenPrefix n)).flatten) :
    gubaEvenPrefix m = gubaEvenPrefix n ∧ k = l := by
  let p := gubaEvenPrefix m
  let q := gubaEvenPrefix n
  let w := (List.replicate k p).flatten
  have he : w = (List.replicate l q).flatten := heq
  have hp : 0 < p.length := by
    have ho := gubaEvenPrefix_odd_length m
    change p.length % 2 = 1 at ho
    omega
  have hq : 0 < q.length := by
    have ho := gubaEvenPrefix_odd_length n
    change q.length % 2 = 1 at ho
    omega
  have hlen : k*p.length = l*q.length := by
    have hh := congrArg List.length he
    simpa [w, repeated_length] using hh
  have hperP : w.HasPeriod p.length := repeat_hasPeriod p k
  have hperQ : w.HasPeriod q.length := by
    rw [he]
    exact repeat_hasPeriod q l
  have hthreshold : p.length+q.length-p.length.gcd q.length ≤ w.length := by
    change _ ≤ (List.replicate k p).flatten.length
    rw [repeated_length]
    exact commonPower_fineWilf_threshold _ _ k l hk hl hlen
  have hg := hperP.gcd hperQ hthreshold
  have hgp : p.HasPeriod (p.length.gcd q.length) :=
    hg.infix (repeat_base_infix p k hk)
  have hqinf : q <:+: w := by
    rw [he]
    exact repeat_base_infix q l hl
  have hgq : q.HasPeriod (p.length.gcd q.length) := hg.infix hqinf
  have hpos := Nat.gcd_pos_of_pos_left q.length hp
  have hdP : p.length.gcd q.length = p.length :=
    gubaEvenPrefix_dividing_period m _ hpos hgp (Nat.gcd_dvd_left _ _)
  have hdQ : p.length.gcd q.length = q.length :=
    gubaEvenPrefix_dividing_period n _ hpos hgq (Nat.gcd_dvd_right _ _)
  have hbase : p.length = q.length := hdP.symm.trans hdQ
  have hkl : k = l := Nat.mul_right_cancel hp (by simpa only [← hbase] using hlen)
  have htP : w.take p.length = p := by
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    change ((List.replicate k p).flatten).take p.length = p
    rw [ht]
    exact repeat_take_base p t
  have htQ : w.take q.length = q := by
    rw [he]
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
    rw [ht]
    exact repeat_take_base q t
  rw [hbase] at htP
  exact ⟨htP.symm.trans htQ,hkl⟩

/-- The full separator-delimited resolvent determines the underlying
selected prefix and exponent, even when compared across ranks. -/
theorem gubaEvenPrefix_resolvent_eq (m n k l : ℕ)
    (hk : 0 < k) (hl : 0 < l)
    (heq : resolventRaw (gubaEvenPrefix m) k =
      resolventRaw (gubaEvenPrefix n) l) :
    gubaEvenPrefix m = gubaEvenPrefix n ∧ k = l := by
  simp only [resolventRaw, longBlock, show k-1+1 = k by omega,
    show l-1+1 = l by omega] at heq
  have hmid := List.append_inj_left' heq rfl
  have hpow := List.append_inj_right hmid rfl
  exact gubaEvenPrefix_commonPower m n k l hk hl hpow


/-- Literal occurrence of a selected resolvent in a selected long word
forces the same base prefix and the prescribed position. This is
cross-prefix uniqueness, not yet the full graded overlap lemma. -/
theorem gubaEvenPrefix_resolvent_occurrence (m n h k : ℕ)
    (p s : List (Fin 2)) (hk : 0 < k)
    (heq : longRaw (gubaEvenPrefix m) h =
      p ++ resolventRaw (gubaEvenPrefix n) k ++ s) :
    gubaEvenPrefix m = gubaEvenPrefix n ∧ k < h ∧
      p.length = (longRaw (gubaEvenPrefix m) (k-1)).length := by
  let q := gubaEvenPrefix m
  let v := gubaEvenPrefix n
  have he : longRaw q h = p ++ resolventRaw v k ++ s := heq
  obtain ⟨j,hj,hpos,hgap⟩ := resolvent_occurrence_gap q v p s
    (gubaPrefix_no_tripleB (2*m+1)) (gubaPrefix_head_zero (2*m+1))
    (gubaPrefix_last_zero (2*m+1))
    (gubaPrefix_no_tripleB (2*n+1)) (gubaPrefix_head_zero (2*n+1))
    (gubaPrefix_last_zero (2*n+1)) h k hk he
  obtain ⟨t,ht⟩ := longRaw_resolvent_factor q (j+1) h (by omega) hj
  rw [show j+1-1 = j by omega] at ht
  have hh : p ++ (resolventRaw v k ++ s) =
      longRaw q j ++ (resolventRaw q (j+1) ++ t) := by
    simpa only [List.append_assoc] using he.symm.trans ht
  have htail := List.append_inj_right hh hpos
  have hrl : (resolventRaw v k).length = (resolventRaw q (j+1)).length := by
    simp only [resolventRaw, List.length_append, longBlock_length,
      List.length_replicate, show k-1+1 = k by omega,
      show j+1-1+1 = j+1 by omega]
    omega
  have hr := List.append_inj_left htail hrl
  obtain ⟨hbase,hidx⟩ := gubaEvenPrefix_resolvent_eq n m k (j+1) hk (by omega) hr
  refine ⟨hbase.symm,by omega,?_⟩
  change p.length = (longRaw q (k-1)).length
  rw [show k-1 = j by omega]
  exact hpos

end QuandleResearch.Issue070
