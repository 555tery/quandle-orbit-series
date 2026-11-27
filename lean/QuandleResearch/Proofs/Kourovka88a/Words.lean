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
    rw [h0, h1, heven, heven] at hh
    exact hh
  · have h0 : p+2*j = 2*(p/2+j)+1 := by omega
    have h1 : p+2*j+d = 2*(p/2+j+d/2)+1 := by omega
    rw [h0, h1, hodd, hodd] at hh
    simpa using hh

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
  have h0 : 2*n+1 ≠ 0 := by omega
  have hp : (2*n+1) % 2 ≠ 0 := by omega
  have hdiv : (2*n+1)/2 = n := by omega
  conv_lhs => rw [thueMorse]
  simp [h0, hp, hdiv]

theorem thueMorse_cubeFree (p d : ℕ) (hd : 0 < d) :
    ¬ CubeAt thueMorse p d :=
  cubeFree_of_binary_rec thueMorse thueMorse_even thueMorse_odd p d hd


/-- The two Boolean symbols as positive generator indices. -/
def thueLetter (n : ℕ) : Fin 2 := if thueMorse n then 1 else 0

theorem thueLetter_eq_iff (i j : ℕ) :
    thueLetter i = thueLetter j ↔ thueMorse i = thueMorse j := by
  unfold thueLetter
  cases hi : thueMorse i <;> cases hj : thueMorse j <;> simp [hi, hj]

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
  have h : thueMorse 0 = false := by decide
  simp [thueLetter, h]

theorem gubaPrefix_second (m : ℕ) :
    (gubaPrefix m)[1]'(by rw [gubaPrefix, thuePrefix_length]; have h := (prefixEnd_eligible m).2.2; omega) = 1 := by
  change (thuePrefix (prefixEnd m+1))[1]'(by rw [thuePrefix_length]; have h := (prefixEnd_eligible m).2.2; omega) = 1
  rw [thuePrefix_get]
  have h : thueMorse 1 = true := by decide
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
    rw [longRaw, weightedLength_positive_mul, weightedLength_longBlock]
    rw [Nat.mul_add, ih]
    ring

theorem weightedLength_longConjugator_twice (q : List (Fin 2)) (m : ℕ) :
    2 * weightedLength (longConjugator (positiveWord q) m) =
      6*m*10^80 + m*(m+1)*weightedLength (positiveWord q) := by
  rw [← positiveWord_longRaw]
  exact weightedLength_longRaw_twice q m

end QuandleResearch.Issue070
