import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy
import SmallPresentation.SmallCancellationDipoleIdentityRibbon
import SmallPresentation.SmallCancellationGeometryIdentityPlanarity
import SmallPresentation.SmallCancellationGeometryIdentityVertexWords

/-!
# Experimental bridge to the pinned Small-Groups geometry library

This file is built by the isolated geometry workflow, not by the default
QuandleResearch target. The external library supplies actual finite row
ribbons, with literal occurrence indices and inverse-labelled edge pairing.
No small-cancellation or rank-survival conclusion is assumed here.

The first bridge is independent of the spellings chosen for the relators.
The specialization below keeps the four literal blocks of each height
relation. Cyclic reduction and admissibility of the selected periods
remain separate obligations.
-/

namespace QuandleResearch.Issue070

open SmallPresentationStatements.RelationCoordinates
open SmallPresentationStatements.RelativeSmallCancellation.Geometry
open SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

variable {I : Type}

/-- Every normal-closure member has a finite signed, conjugated-row expression.
Reuse the upstream surjective normal evaluation and its list evaluation lemma. -/
theorem exists_peiffer_expression (rel : I → F) (w : F)
    (hw : w ∈ Subgroup.normalClosure (Set.range rel)) :
    ∃ s : Peiffer.Sequence F I, Peiffer.evaluation rel s = w := by
  classical
  obtain ⟨v, hv⟩ := normalEvaluation_surjective rel ⟨w, hw⟩
  refine ⟨v.toWord, ?_⟩
  rw [← Peiffer.evaluation_mk, FreeGroup.mk_toWord]
  exact congrArg Subtype.val hv

/-- A separate label for the boundary, not a relator of any rank. -/
def markedRows (rows : I → RawWord) (w : F) : Option I → RawWord
  | none => w.toWord
  | some i => rows i

def markOccurrence (a : Peiffer.Occurrence F I) : Peiffer.Occurrence F (Option I) :=
  ((a.1.1, some a.1.2), a.2)

theorem marked_evaluation (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I) :
    Peiffer.evaluation (fun i => FreeGroup.mk (markedRows rows w i))
        (s.map markOccurrence) =
      Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change Peiffer.term (fun i => FreeGroup.mk (markedRows rows w i))
        (markOccurrence x) *
        Peiffer.evaluation (fun i => FreeGroup.mk (markedRows rows w i))
          (xs.map markOccurrence) =
      Peiffer.term (fun i => FreeGroup.mk (rows i)) x *
        Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) xs
    rw [ih]
    rfl

/-- Prepend the inverse boundary word, so the full expression evaluates to 1.
All other rows retain their original indices and signs. -/
def boundaryIdentity (s : Peiffer.Sequence F I) : Peiffer.Sequence F (Option I) :=
  ((1, none), false) :: s.map markOccurrence

theorem boundaryIdentity_evaluation (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w) :
    Peiffer.evaluation (fun i => FreeGroup.mk (markedRows rows w i))
      (boundaryIdentity s) = 1 := by
  change Peiffer.term (fun i => FreeGroup.mk (markedRows rows w i))
      ((1, none), false) *
      Peiffer.evaluation (fun i => FreeGroup.mk (markedRows rows w i))
        (s.map markOccurrence) = 1
  rw [marked_evaluation, hs]
  simp [Peiffer.term, markedRows, FreeGroup.mk_toWord]

theorem boundaryIdentity_only_marked (s : Peiffer.Sequence F I) :
    ∀ x ∈ (boundaryIdentity s).tail, x.1.2 ≠ none := by
  intro x hx
  change x ∈ s.map markOccurrence at hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  simp [markOccurrence]

/-- Construct a finite inverse-labelled ribbon using the upstream constructor.
This is a realization of the marked identity; its components are planar
by the upstream theorem. It is not yet a connected reduced diagram. -/
noncomputable def boundaryRibbon (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w) :=
  relatorRibbon (chosenSection (Fin 2)) (markedRows rows w)
    (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs)

/-- The original rank and integer height are kept as a row label.
The marked boundary uses none, not a fabricated rank. -/
abbrev RankHeight (n : ℕ) := Fin n × ℤ

noncomputable def rankHeightRel (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (i : RankHeight n) : F :=
  weightedRankHeightRelator pick X i.1.val i.2

theorem rankHeight_normalClosure (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) :
    Subgroup.normalClosure (Set.range (rankHeightRel pick X n)) =
      weightedHeightStage pick X n := by
  unfold weightedHeightStage
  congr 1
  ext w
  constructor
  · rintro ⟨⟨i,k⟩, rfl⟩
    exact ⟨i.val, i.isLt, k, rfl⟩
  · rintro ⟨i, hi, k, rfl⟩
    exact ⟨(⟨i,hi⟩,k), rfl⟩

/-- Use the selected period and conjugator, keeping the literal height
blocks. Inactive ranks contribute the empty word. -/
noncomputable def rankHeightRows (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (i : RankHeight n) : RawWord := by
  classical
  let N := weightedStages pick X i.1.val
  exact if h : ∃ w : F, ¬ Good N w then
    let c := (pick N h).val
    literalHeightWord (X i.1.val N c) c i.2
  else []

theorem rankHeightRows_eval (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (i : RankHeight n) :
    FreeGroup.mk (rankHeightRows pick X n i) = rankHeightRel pick X n i := by
  classical
  by_cases h : ∃ w : F, ¬ Good (weightedStages pick X i.1.val) w
  · simp only [rankHeightRows, rankHeightRel, weightedRankHeightRelator,
      dite_eq_left h, literalHeightWord_eval]
  · simp only [rankHeightRows, rankHeightRel, weightedRankHeightRelator,
      dite_eq_right h]
    rfl

theorem exists_rankHeight_identity (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      Peiffer.evaluation (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w := by
  rw [← rankHeight_normalClosure] at hw
  obtain ⟨s, hs⟩ := exists_peiffer_expression (rankHeightRel pick X n) w hw
  exact ⟨s, by simpa only [rankHeightRows_eval] using hs⟩

/-- Instantiate the imported ribbon construction with the actual stage
and boundary word, retaining the rank-height labels. -/
noncomputable def rankHeightRibbon (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :=
  boundaryRibbon (rankHeightRows pick X n) w
    (Classical.choose (exists_rankHeight_identity pick X n w hw))
    (Classical.choose_spec (exists_rankHeight_identity pick X n w hw))

#print axioms exists_peiffer_expression
#print axioms marked_evaluation
#print axioms boundaryIdentity_evaluation
#print axioms boundaryIdentity_only_marked
#print axioms boundaryRibbon
#print axioms rankHeight_normalClosure
#print axioms rankHeightRows_eval
#print axioms exists_rankHeight_identity
#print axioms rankHeightRibbon


/-- Every component of the actual marked ribbon has the spherical Euler
property. This is a direct use of the upstream realization theorem,
not a postulated planarity condition. -/
theorem boundaryRibbon_euler (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w) :
    (boundaryRibbon rows w s hs).EulerEquality := by
  exact relatorRibbon_euler (chosenSection (Fin 2)) (markedRows rows w)
    (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs)

theorem rankHeightRibbon_euler (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    (rankHeightRibbon pick X n w hw).EulerEquality := by
  unfold rankHeightRibbon
  apply boundaryRibbon_euler

#print axioms boundaryRibbon_euler
#print axioms rankHeightRibbon_euler


/-! ## The connected component of the unique marked boundary

For a nonidentity boundary the initial marked row is nonempty. The
upstream occurrence/vertex equivalence makes it a genuine vertex,
and restriction preserves its entire cyclic reading.
-/

def boundaryOccurrence (s : Peiffer.Sequence F I) :
    Fin (boundaryIdentity s).length := ⟨0, by simp [boundaryIdentity]⟩

theorem boundaryOccurrence_pos (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I) (hw : w ≠ 1) :
    0 < (orientedWord
      (markedRows rows w (boundaryIdentity s)[boundaryOccurrence s].1.2)
      (boundaryIdentity s)[boundaryOccurrence s].2).length := by
  change 0 < (orientedWord w.toWord false).length
  rw [orientedWord_length]
  by_contra! hn
  have hnil : w.toWord = [] := List.length_eq_zero_iff.mp (by omega)
  exact hw (FreeGroup.toWord_eq_nil_iff.mp hnil)

def boundaryDart (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I) (hw : w ≠ 1) :
    DiscDarts (markedRows rows w) (boundaryIdentity s) :=
  discAt (markedRows rows w) (boundaryIdentity s) (boundaryOccurrence s)
    ⟨0, boundaryOccurrence_pos rows w s hw⟩

theorem boundaryDart_occurrence (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I) (hw : w ≠ 1) :
    discOccurrence (markedRows rows w) (boundaryIdentity s)
      (boundaryDart rows w s hw) = boundaryOccurrence s :=
  discOccurrence_at _ _ _ _

/-- The vertex of the marked dart is precisely the original boundary
occurrence, not any interior occurrence with the same group value. -/
theorem boundaryDart_sameVertex_iff (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) (d : DiscDarts (markedRows rows w) (boundaryIdentity s)) :
    (boundaryRibbon rows w s hs).rotation.SameCycle (boundaryDart rows w s hw) d ↔
      discOccurrence (markedRows rows w) (boundaryIdentity s) d =
        boundaryOccurrence s := by
  change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle
    (boundaryDart rows w s hw) d ↔ _
  rw [disc_sameCycle_iff, boundaryDart_occurrence, eq_comm]

/-- Reading the original zero corner gives the inverse of the entire
boundary word, not merely a group element or an unspecified rotation. -/
theorem boundaryRibbon_read (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    ((boundaryRibbon rows w s hs).vertexBoundary (boundaryDart rows w s hw)).map
      (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) =
      FreeGroup.invRev w.toWord := by
  exact vertex_read_at_zero (chosenSection (Fin 2)) (markedRows rows w)
    (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs)
    (boundaryOccurrence s) (boundaryOccurrence_pos rows w s hw)

noncomputable def boundaryComponent (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :=
  (boundaryRibbon rows w s hs).componentRibbon (boundaryDart rows w s hw)

theorem boundaryComponent_connected (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    (boundaryComponent rows w s hs hw).Connected :=
  (boundaryRibbon rows w s hs).componentRibbon_connected _

theorem boundaryComponent_sphere (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    Fintype.card (boundaryComponent rows w s hs hw).Vertex +
      Fintype.card (boundaryComponent rows w s hs hw).Face =
    Fintype.card (boundaryComponent rows w s hs hw).Edge + 2 :=
  (boundaryRibbon rows w s hs).componentRibbon_sphere
    (boundaryRibbon_euler rows w s hs) _

#print axioms boundaryOccurrence_pos
#print axioms boundaryDart_occurrence
#print axioms boundaryDart_sameVertex_iff
#print axioms boundaryRibbon_read
#print axioms boundaryComponent
#print axioms boundaryComponent_connected
#print axioms boundaryComponent_sphere

#print axioms markedRows
#print axioms markOccurrence
#print axioms boundaryIdentity
#print axioms RankHeight
#print axioms rankHeightRel
#print axioms rankHeightRows
#print axioms boundaryOccurrence
#print axioms boundaryDart


/-! ## Exact row readings for the recursive construction

Keep the active rank and the integer height visible in the geometric
realization. Empty rows never give an interior dart. The signed row
reading below is literal; it does not assert cyclic reduction.
-/

/-- At an active rank, the actual presentation row has precisely the
two signed long sides of the recursively chosen word. -/
theorem guba_rankHeightRows_active (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n)
    (h : ∃ w : F, ¬ Good (gubaState pick i.1.val).1 w)
    (hk : i.2 ≠ 0) :
    rankHeightRows pick (gubaConjugatorChoice pick) n i =
      (activeLongWord pick i.1.val h).map (fun x => (x,true)) ++
      rawIntPow (pick (gubaState pick i.1.val).1 h).val.toWord i.2 ++
      FreeGroup.invRev ((activeLongWord pick i.1.val h).map (fun x => (x,true))) ++
      FreeGroup.invRev (rawIntPow a.toWord i.2) := by
  classical
  unfold rankHeightRows
  rw [← gubaState_stage pick i.1.val]
  simp only [dite_eq_left h]
  exact literalHeightWord_positive_sides (activeLongWord pick i.1.val h) _ _ hk

/-- An inactive rank or zero height has no nonempty row. Thus every
interior dart comes from an active rank at nonzero height. -/
theorem guba_rankHeightRows_nonempty (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n)
    (hne : rankHeightRows pick (gubaConjugatorChoice pick) n i ≠ []) :
    (∃ w : F, ¬ Good (gubaState pick i.1.val).1 w) ∧ i.2 ≠ 0 := by
  classical
  have hrow := hne
  unfold rankHeightRows at hrow
  rw [← gubaState_stage pick i.1.val] at hrow
  by_cases h : ∃ w : F, ¬ Good (gubaState pick i.1.val).1 w
  · refine ⟨h, ?_⟩
    intro hk
    apply hrow
    rw [dite_eq_left h, hk, literalHeightWord_zero]
  · exact False.elim (hrow (dite_eq_right h))

/-- Read any nonempty interior occurrence at its original zero corner.
Unlike a statement about evaluation in the group, this preserves the
full signed list, including its four distinguished blocks. -/
theorem boundaryRibbon_interior_read (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (j : Fin (boundaryIdentity s).length) (i : I)
    (hi : (boundaryIdentity s)[j].1.2 = some i)
    (hp : 0 < (orientedWord
      (markedRows rows w (boundaryIdentity s)[j].1.2)
      (boundaryIdentity s)[j].2).length) :
    ((boundaryRibbon rows w s hs).vertexBoundary
      (discAt (markedRows rows w) (boundaryIdentity s) j ⟨0,hp⟩)).map
      (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) =
      orientedWord (rows i) (boundaryIdentity s)[j].2 := by
  have hr := vertex_read_at_zero (chosenSection (Fin 2)) (markedRows rows w)
    (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs) j hp
  exact hr.trans (congrArg (fun label =>
    orientedWord (markedRows rows w label) (boundaryIdentity s)[j].2) hi)

/-- Weight of a signed row is independent of the orientation of the
occurrence. The inverse orientation uses Mathlib's exact inverse word. -/
theorem orientedWord_rawWeight (v : RawWord) (sign : Bool) :
    rawWeight (orientedWord v sign) = rawWeight v := by
  cases sign
  · exact rawWeight_invRev v
  · rfl

/-- Each actual paired dart has the inverse signed letter. For a list of
paired darts, reversing the order therefore reads exactly the inverse
word. This imposes no claim that the lists form contiguous paths. -/
theorem boundaryRibbon_inverse_read (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (ds : List (DiscDarts (markedRows rows w) (boundaryIdentity s))) :
    ((ds.map (boundaryRibbon rows w s hs).edge).reverse).map
      (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) =
      FreeGroup.invRev (ds.map
        (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) := by
  rw [List.map_reverse, List.map_map, FreeGroup.invRev, List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d _
  exact relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
    (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs) d

#print axioms guba_rankHeightRows_active
#print axioms guba_rankHeightRows_nonempty
#print axioms boundaryRibbon_interior_read
#print axioms orientedWord_rawWeight
#print axioms boundaryRibbon_inverse_read


/-! ## Directly paired boundary segments

A literal factor of a based boundary reading lifts to a consecutive
list of darts in that boundary. If two such segments on the long
sides are paired edge-for-edge in opposite orders, the two positive
factors coincide. This is the direct adjacency case, not the general
case of contiguity through a lower-rank subdiagram.
-/

/-- A three-block decomposition of the reading lifts to a three-block
decomposition of the original dart list, with all readings retained. -/
theorem read_factor_lift {D : Type} (read : D → Letter) (ds : List D)
    (p z r : RawWord) (h : ds.map read = p ++ z ++ r) :
    ∃ dp dz dr : List D, ds = dp ++ dz ++ dr ∧
      dp.map read = p ∧ dz.map read = z ∧ dr.map read = r := by
  obtain ⟨dpr,dr,hds,hpr,hr⟩ := List.map_eq_append_iff.mp h
  obtain ⟨dp,dz,hdpr,hp,hz⟩ := List.map_eq_append_iff.mp hpr
  exact ⟨dp,dz,dr,by rw [hds,hdpr],hp,hz,hr⟩

/-- Extract the actual consecutive darts for a literal factor of an
interior row, at the original zero corner. -/
theorem boundaryRibbon_interior_factor (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (j : Fin (boundaryIdentity s).length) (i : I)
    (hi : (boundaryIdentity s)[j].1.2 = some i)
    (hp : 0 < (orientedWord
      (markedRows rows w (boundaryIdentity s)[j].1.2)
      (boundaryIdentity s)[j].2).length)
    (p z r : RawWord)
    (hf : orientedWord (rows i) (boundaryIdentity s)[j].2 = p ++ z ++ r) :
    ∃ dp dz dr : List (DiscDarts (markedRows rows w) (boundaryIdentity s)),
      (boundaryRibbon rows w s hs).vertexBoundary
        (discAt (markedRows rows w) (boundaryIdentity s) j ⟨0,hp⟩) =
          dp ++ dz ++ dr ∧
      dp.map (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) = p ∧
      dz.map (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) = z ∧
      dr.map (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) = r := by
  exact read_factor_lift _ _ p z r
    ((boundaryRibbon_interior_read rows w s hs j i hi hp).trans hf)

/-- A directly paired pair of dart lists on oppositely read positive
sides has the same underlying positive factor. -/
theorem boundaryRibbon_paired_positive_eq (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (ds dt : List (DiscDarts (markedRows rows w) (boundaryIdentity s)))
    (z t : List (Fin 2))
    (hpair : dt = (ds.map (boundaryRibbon rows w s hs).edge).reverse)
    (hz : ds.map (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) =
      z.map (fun x => (x,true)))
    (ht : dt.map (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)) =
      FreeGroup.invRev (t.map (fun x => (x,true)))) :
    z = t := by
  have he := boundaryRibbon_inverse_read rows w s hs ds
  rw [← hpair,hz,ht] at he
  have hm := FreeGroup.invRev_injective he
  have hf := congrArg (List.map (Prod.fst : Letter → Fin 2)) hm
  simp only [List.map_map] at hf
  change t.map (fun x => x) = z.map (fun x => x) at hf
  simpa only [List.map_id'] using hf.symm

/-- Weighted bound for a directly paired segment lying in opposite
long sides. The two factor decompositions specify the locations in
the positive words; equality of the factors is deduced from the
actual edge pairing rather than assumed. -/
theorem boundaryRibbon_direct_long_overlap (pick : WeightedSelector)
    (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick (gubaConjugatorChoice pick) n i)) s = w)
    (ds dt : List (DiscDarts
      (markedRows (rankHeightRows pick (gubaConjugatorChoice pick) n) w)
      (boundaryIdentity s)))
    (i j : RankHeight n)
    (hi : ∃ v : F, ¬ Good (gubaState pick i.1.val).1 v)
    (hj : ∃ v : F, ¬ Good (gubaState pick j.1.val).1 v)
    (p z r u t v : List (Fin 2))
    (hfirst : activeLongWord pick i.1.val hi = p ++ z ++ r)
    (hsecond : activeLongWord pick j.1.val hj = u ++ t ++ v)
    (hdiff : i.1.val ≠ j.1.val ∨ p.length ≠ u.length)
    (hpair : dt = (ds.map
      (boundaryRibbon (rankHeightRows pick (gubaConjugatorChoice pick) n) w s hs).edge).reverse)
    (hz : ds.map (discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick (gubaConjugatorChoice pick) n) w) (boundaryIdentity s)) =
      z.map (fun x => (x,true)))
    (ht : dt.map (discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick (gubaConjugatorChoice pick) n) w) (boundaryIdentity s)) =
      FreeGroup.invRev (t.map (fun x => (x,true)))) :
    240*10^17*rawWeight (ds.map (discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick (gubaConjugatorChoice pick) n) w) (boundaryIdentity s))) ≤
      min (positiveWeight (activeLongWord pick i.1.val hi))
        (positiveWeight (activeLongWord pick j.1.val hj)) := by
  have he := boundaryRibbon_paired_positive_eq _ w s hs ds dt z t hpair hz ht
  rw [← he] at hsecond
  rw [hz, ← positiveWeight_eq_rawWeight_map]
  exact activeLongWord_overlap_bound_both pick i.1.val j.1.val hi hj
    p z r u v hfirst hsecond hdiff

#print axioms read_factor_lift
#print axioms boundaryRibbon_interior_factor
#print axioms boundaryRibbon_paired_positive_eq
#print axioms boundaryRibbon_direct_long_overlap


/-! ## Perimeter and the final survival threshold

Only the literal perimeters are used here. A large-cell perimeter
estimate for nontrivial kernel words must still be proved by the
graded-diagram induction; it is not supplied by Euler equality alone.
-/

/-- Every nonempty active height row has two long sides and the two
power sides, with their exact weights before any seam reductions. -/
theorem guba_rankHeightRows_weight (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n)
    (h : ∃ w : F, ¬ Good (gubaState pick i.1.val).1 w)
    (hk : i.2 ≠ 0) :
    rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) =
      2 * positiveWeight (activeLongWord pick i.1.val h) +
      i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val +
      i.2.natAbs := by
  rw [guba_rankHeightRows_active pick n i h hk]
  simp only [rawWeight_append, rawWeight_invRev, ← positiveWeight_eq_rawWeight_map]
  have hc := minBad_intPow_weight (pick (gubaState pick i.1.val).1 h).property i.2
  unfold weightedLength at hc
  rw [minBad_intPow_toWord (pick (gubaState pick i.1.val).1 h).property] at hc
  have ha : rawWeight (rawIntPow a.toWord i.2) = i.2.natAbs := by
    cases i with
    | mk j k =>
      change rawWeight (rawIntPow a.toWord k) = k.natAbs
      have h1 : rawWeight a.toWord = 1 := by
        change weightedLength a = 1
        have h := weightedLength_a_zpow 1
        rw [zpow_one] at h
        exact h
      cases k with
      | ofNat m =>
        change rawWeight (rawNatPow a.toWord m) = m
        rw [rawWeight_rawNatPow, h1, mul_one]
      | negSucc m =>
        change rawWeight (FreeGroup.invRev (rawNatPow a.toWord (m+1))) = m+1
        rw [rawWeight_invRev, rawWeight_rawNatPow, h1, mul_one]
  rw [hc, ha]
  unfold weightedLength
  omega

/-- The first term of the exact long-word formula already makes every
nonempty row much longer than the boundary of the commutator. -/
theorem guba_rankHeightRows_large (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n)
    (hne : rankHeightRows pick (gubaConjugatorChoice pick) n i ≠ []) :
    5 * (2 + 2 * 10^80) <
      4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) := by
  obtain ⟨h,hk⟩ := guba_rankHeightRows_nonempty pick n i hne
  rw [guba_rankHeightRows_weight pick n i h hk]
  have hs := weightedLength_longRaw_twice (activePrefix pick i.1.val h) (10^20)
  change 2 * positiveWeight (activeLongWord pick i.1.val h) =
    6 * (10^20 : ℕ) * 10^80 +
      10^20 * (10^20+1) * positiveWeight (activePrefix pick i.1.val h) at hs
  norm_num at hs ⊢
  omega

/-- The remaining large-cell estimate suffices for the exact target.
Its premise is a statement about the actual recursively chosen
all-height rows, not about an arbitrary presentation. No such estimate
is assumed anywhere in the construction or in its earlier lemmas. -/
theorem answer_of_guba_large_cell (pick : WeightedSelector)
    (hcell : ∀ n (w : F),
      w ∈ weightedHeightStage pick (gubaConjugatorChoice pick) n →
      w ≠ 1 → ∃ i : RankHeight n,
        rankHeightRows pick (gubaConjugatorChoice pick) n i ≠ [] ∧
        4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) <
          5 * weightedLength w) :
    answer := by
  apply answer_of_heightStages_short pick (gubaConjugatorChoice pick)
  intro n w hw hlen
  by_contra hne
  obtain ⟨i,hi,hl⟩ := hcell n w hw hne
  have hlarge := guba_rankHeightRows_large pick n i hi
  omega

#print axioms guba_rankHeightRows_weight
#print axioms guba_rankHeightRows_large
#print axioms answer_of_guba_large_cell


/-! ## Minimal signed expressions and admissible algebraic mergers

Minimize the number of interior occurrences for the fixed boundary
value. Replacement of consecutive factors by a shorter expression
with the same evaluation is then impossible. This is a statement
about signed expressions; a planar contiguity surgery must separately
produce the required replacement expression.
-/

def MinimalExpression (rel : I → F) (w : F)
    (s : Peiffer.Sequence F I) : Prop :=
  Peiffer.evaluation rel s = w ∧
    ∀ t : Peiffer.Sequence F I, Peiffer.evaluation rel t = w →
      s.length ≤ t.length

/-- Any element of the normal closure has a minimal signed expression. -/
theorem exists_minimalExpression (rel : I → F) (w : F)
    (hw : w ∈ Subgroup.normalClosure (Set.range rel)) :
    ∃ s : Peiffer.Sequence F I, MinimalExpression rel w s := by
  classical
  obtain ⟨s, hs⟩ := exists_peiffer_expression rel w hw
  have hex : ∃ m : ℕ, ∃ t : Peiffer.Sequence F I,
      Peiffer.evaluation rel t = w ∧ t.length = m :=
    ⟨s.length, s, hs, rfl⟩
  obtain ⟨t, ht, hlen⟩ := Nat.find_spec hex
  refine ⟨t, ht, ?_⟩
  intro u hu
  rw [hlen]
  exact Nat.find_min' hex ⟨u,hu,rfl⟩

theorem peiffer_evaluation_append (rel : I → F)
    (s t : Peiffer.Sequence F I) :
    Peiffer.evaluation rel (s ++ t) =
      Peiffer.evaluation rel s * Peiffer.evaluation rel t := by
  simp only [Peiffer.evaluation, List.map_append, List.prod_append]

/-- Any equivalent replacement of a consecutive block in a minimal
expression has at least as many occurrences as that block. -/
theorem minimalExpression_block_length (rel : I → F) (w : F)
    (p b r t : Peiffer.Sequence F I)
    (hmin : MinimalExpression rel w (p ++ b ++ r))
    (he : Peiffer.evaluation rel b = Peiffer.evaluation rel t) :
    b.length ≤ t.length := by
  have ht : Peiffer.evaluation rel (p ++ t ++ r) = w := by
    rw [peiffer_evaluation_append, peiffer_evaluation_append, ← he]
    simpa only [peiffer_evaluation_append] using hmin.1
  have hl := hmin.2 (p ++ t ++ r) ht
  simp only [List.length_append] at hl
  omega

/-- No consecutive inverse-valued pair survives in a minimal
expression, irrespective of whether its two labels are equal. -/
theorem minimalExpression_no_cancel_pair (rel : I → F) (w : F)
    (p r : Peiffer.Sequence F I) (x y : Peiffer.Occurrence F I)
    (hmin : MinimalExpression rel w (p ++ [x,y] ++ r)) :
    Peiffer.term rel x * Peiffer.term rel y ≠ 1 := by
  intro he
  have hb : Peiffer.evaluation rel [x,y] =
      Peiffer.evaluation rel [] := by
    simpa [Peiffer.evaluation] using he
  have hl := minimalExpression_block_length rel w p [x,y] r [] hmin hb
  simp at hl

/-- A minimal expression never contains a trivial-valued occurrence. -/
theorem minimalExpression_no_trivial_term (rel : I → F) (w : F)
    (p r : Peiffer.Sequence F I) (x : Peiffer.Occurrence F I)
    (hmin : MinimalExpression rel w (p ++ [x] ++ r)) :
    Peiffer.term rel x ≠ 1 := by
  intro he
  have hb : Peiffer.evaluation rel [x] =
      Peiffer.evaluation rel [] := by
    simpa [Peiffer.evaluation] using he
  have hl := minimalExpression_block_length rel w p [x] r [] hmin hb
  simp at hl

/-- The actual all-height presentation admits a minimal expression,
with the original rank and height labels retained. -/
theorem exists_minimal_rankHeight_expression (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      MinimalExpression (rankHeightRel pick X n) w s := by
  rw [← rankHeight_normalClosure] at hw
  exact exists_minimalExpression _ w hw

/-- A pair at one rank with the relative based conjugator prescribed
by the height-addition identity compresses to one occurrence. This
rules out that particular algebraic pattern in a minimal expression;
it does not assume that all geometrically adjacent cells have it. -/
theorem minimal_rankHeight_no_merge_pair (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (j : Fin n) (k l : ℤ) (u : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (hmin : MinimalExpression (rankHeightRel pick X n) w
      (p ++ [((u,(j,k)),true), ((u*a^k,(j,l)),true)] ++ r)) :
    False := by
  let rel := rankHeightRel pick X n
  let b : Peiffer.Sequence F (RankHeight n) :=
    [((u,(j,k)),true), ((u*a^k,(j,l)),true)]
  let t : Peiffer.Sequence F (RankHeight n) := [((u,(j,k+l)),true)]
  have hb : Peiffer.evaluation rel b = Peiffer.evaluation rel t := by
    simp only [b, t, Peiffer.evaluation, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Peiffer.term, Bool.cond_true]
    change (u * weightedRankHeightRelator pick X j.val k * u⁻¹) *
      ((u*a^k) * weightedRankHeightRelator pick X j.val l * (u*a^k)⁻¹) =
      u * weightedRankHeightRelator pick X j.val (k+l) * u⁻¹
    rw [weightedRankHeightRelator_add]
    group
  have hl := minimalExpression_block_length rel w p b r t hmin hb
  change 2 ≤ 1 at hl
  omega

#print axioms MinimalExpression
#print axioms exists_minimalExpression
#print axioms peiffer_evaluation_append
#print axioms minimalExpression_block_length
#print axioms minimalExpression_no_cancel_pair
#print axioms minimalExpression_no_trivial_term
#print axioms exists_minimal_rankHeight_expression
#print axioms minimal_rankHeight_no_merge_pair


/-! ## Absorb orientation into signed heights

The all-height family is closed under inversion up to a based change
of conjugator. Thus choosing a minimal expression does not require
positive and negative orientations as separate algebraic cases.
-/

theorem rankHeightRel_neg (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (j : Fin n) (k : ℤ) :
    rankHeightRel pick X n (j,-k) =
      (a^k)⁻¹ * (rankHeightRel pick X n (j,k))⁻¹ * a^k := by
  classical
  by_cases h : ∃ w : F, ¬ Good (weightedStages pick X j.val) w
  · simp only [rankHeightRel, weightedRankHeightRelator, dite_eq_left h]
    exact heightRelator_neg _ _ k
  · simp [rankHeightRel, weightedRankHeightRelator, h]

/-- Replace a negatively oriented occurrence by the opposite height,
with the basepoint adjusted along the a-side. -/
def positiveHeightOccurrence (n : ℕ) :
    Peiffer.Occurrence F (RankHeight n) → Peiffer.Occurrence F (RankHeight n)
  | ((u,(j,k)),true) => ((u,(j,k)),true)
  | ((u,(j,k)),false) => ((u*a^k,(j,-k)),true)

theorem positiveHeightOccurrence_term (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ)
    (x : Peiffer.Occurrence F (RankHeight n)) :
    Peiffer.term (rankHeightRel pick X n) (positiveHeightOccurrence n x) =
      Peiffer.term (rankHeightRel pick X n) x := by
  rcases x with ⟨⟨u,⟨j,k⟩⟩,b⟩
  cases b
  · change (u*a^k) * rankHeightRel pick X n (j,-k) * (u*a^k)⁻¹ =
        (u * rankHeightRel pick X n (j,k) * u⁻¹)⁻¹
    rw [rankHeightRel_neg]
    group
  · rfl

theorem positiveHeightOccurrence_sign (n : ℕ)
    (x : Peiffer.Occurrence F (RankHeight n)) :
    (positiveHeightOccurrence n x).2 = true := by
  rcases x with ⟨⟨u,⟨j,k⟩⟩,b⟩
  cases b <;> rfl

theorem positiveHeightOccurrence_rank (n : ℕ)
    (x : Peiffer.Occurrence F (RankHeight n)) :
    (positiveHeightOccurrence n x).1.2.1 = x.1.2.1 := by
  rcases x with ⟨⟨u,⟨j,k⟩⟩,b⟩
  cases b <;> rfl

theorem positiveHeightOccurrence_evaluation (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ)
    (s : Peiffer.Sequence F (RankHeight n)) :
    Peiffer.evaluation (rankHeightRel pick X n) (s.map (positiveHeightOccurrence n)) =
      Peiffer.evaluation (rankHeightRel pick X n) s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change Peiffer.term (rankHeightRel pick X n) (positiveHeightOccurrence n x) *
        Peiffer.evaluation (rankHeightRel pick X n) (xs.map (positiveHeightOccurrence n)) =
      Peiffer.term (rankHeightRel pick X n) x *
        Peiffer.evaluation (rankHeightRel pick X n) xs
    rw [positiveHeightOccurrence_term, ih]

/-- Every finite-stage kernel member admits a minimal expression
whose occurrences have positive orientation and signed heights. -/
theorem exists_positive_minimal_rankHeight_expression (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      MinimalExpression (rankHeightRel pick X n) w s ∧
      ∀ x ∈ s, x.2 = true := by
  obtain ⟨s,hs⟩ := exists_minimal_rankHeight_expression pick X n w hw
  refine ⟨s.map (positiveHeightOccurrence n), ⟨?_,?_⟩, ?_⟩
  · rw [positiveHeightOccurrence_evaluation]
    exact hs.1
  · intro t ht
    rw [List.length_map]
    exact hs.2 t ht
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact positiveHeightOccurrence_sign n y

/-- No zero-height occurrence can occur anywhere in a minimal
expression. The proof does not require a chosen cyclic cut. -/
theorem minimal_rankHeight_nonzero_height (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : MinimalExpression (rankHeightRel pick X n) w s)
    (x : Peiffer.Occurrence F (RankHeight n)) (hx : x ∈ s) :
    x.1.2.2 ≠ 0 := by
  obtain ⟨p,r,he⟩ := List.mem_iff_append.mp hx
  have hsplit : s = p ++ [x] ++ r := by simpa using he
  have hm : MinimalExpression (rankHeightRel pick X n) w (p ++ [x] ++ r) :=
    hsplit ▸ hs
  intro hz
  apply minimalExpression_no_trivial_term _ w p r x hm
  rcases x with ⟨⟨u,⟨j,k⟩⟩,b⟩
  change k = 0 at hz
  subst k
  cases b <;> simp [Peiffer.term, rankHeightRel, weightedRankHeightRelator_zero]

#print axioms rankHeightRel_neg
#print axioms positiveHeightOccurrence
#print axioms positiveHeightOccurrence_term
#print axioms positiveHeightOccurrence_sign
#print axioms positiveHeightOccurrence_rank
#print axioms positiveHeightOccurrence_evaluation
#print axioms exists_positive_minimal_rankHeight_expression
#print axioms minimal_rankHeight_nonzero_height


/-! ## Move separated occurrences together before merging

The intermediate block need not be empty. Moving a cell past it changes
the based conjugator by its evaluated boundary word. This is an
algebraic Peiffer exchange, preserving all intervening occurrences,
rather than an assumption that the cells were consecutive in the
original expression.
-/

/-- Shift an occurrence across an intervening product on its left. -/
def shiftOccurrence (g : F) (x : Peiffer.Occurrence F I) :
    Peiffer.Occurrence F I :=
  ((g*x.1.1,x.1.2),x.2)

theorem shiftOccurrence_term (rel : I → F) (g : F)
    (x : Peiffer.Occurrence F I) :
    Peiffer.term rel (shiftOccurrence g x) =
      g * Peiffer.term rel x * g⁻¹ := by
  rcases x with ⟨⟨u,i⟩,b⟩
  cases b <;> simp only [shiftOccurrence, Peiffer.term, Bool.cond_true,
    Bool.cond_false] <;> group

/-- Moving a signed occurrence past a whole intervening block preserves
the product and does not delete or duplicate any occurrence. -/
theorem peiffer_move_occurrence (rel : I → F)
    (m : Peiffer.Sequence F I) (y : Peiffer.Occurrence F I) :
    Peiffer.evaluation rel (m ++ [y]) =
      Peiffer.evaluation rel
        ([shiftOccurrence (Peiffer.evaluation rel m) y] ++ m) := by
  have hs (x : Peiffer.Occurrence F I) :
      Peiffer.evaluation rel [x] = Peiffer.term rel x := by
    simp [Peiffer.evaluation]
  simp only [peiffer_evaluation_append, hs, shiftOccurrence_term]
  group

/-- Equal-valued expressions of equal length have the same minimality
status, so Peiffer exchanges preserve minimum cardinality. -/
theorem minimalExpression_of_equal_value_length (rel : I → F) (w : F)
    (s t : Peiffer.Sequence F I)
    (hs : MinimalExpression rel w s)
    (he : Peiffer.evaluation rel s = Peiffer.evaluation rel t)
    (hl : s.length = t.length) :
    MinimalExpression rel w t := by
  refine ⟨he.symm.trans hs.1, ?_⟩
  intro v hv
  rw [← hl]
  exact hs.2 v hv

/-- A separated pair may be moved into consecutive positions without
changing minimality, using the exact product of the intervening block. -/
theorem minimalExpression_move_pair (rel : I → F) (w : F)
    (p m r : Peiffer.Sequence F I) (x y : Peiffer.Occurrence F I)
    (hs : MinimalExpression rel w (p ++ [x] ++ m ++ [y] ++ r)) :
    MinimalExpression rel w
      (p ++ [x, shiftOccurrence (Peiffer.evaluation rel m) y] ++ m ++ r) := by
  apply minimalExpression_of_equal_value_length rel w _ _ hs
  · have he := peiffer_move_occurrence rel m y
    have he' := congrArg (fun v : F =>
      Peiffer.evaluation rel (p ++ [x]) * v * Peiffer.evaluation rel r) he
    simpa only [Peiffer.evaluation, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc] using he'
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Same-rank mergers are forbidden even when the two occurrences are
separated by an arbitrary block, provided the based conjugator after
moving across that block has the required a-power offset. -/
theorem minimal_rankHeight_no_separated_merge_pair (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (j : Fin n) (k l : ℤ) (u v : F)
    (p m r : Peiffer.Sequence F (RankHeight n))
    (hs : MinimalExpression (rankHeightRel pick X n) w
      (p ++ [((u,(j,k)),true)] ++ m ++ [((v,(j,l)),true)] ++ r))
    (hbase : Peiffer.evaluation (rankHeightRel pick X n) m * v = u*a^k) :
    False := by
  have hm := minimalExpression_move_pair (rankHeightRel pick X n) w p m r
    ((u,(j,k)),true) ((v,(j,l)),true) hs
  apply minimal_rankHeight_no_merge_pair pick X n w j k l u p (m ++ r)
  simpa only [shiftOccurrence, hbase, List.append_assoc] using hm

#print axioms shiftOccurrence
#print axioms shiftOccurrence_term
#print axioms peiffer_move_occurrence
#print axioms minimalExpression_of_equal_value_length
#print axioms minimalExpression_move_pair
#print axioms minimal_rankHeight_no_separated_merge_pair


/-! ## Rank-sensitive minimization

A minimum total number of cells need not be minimal for graded
cancellation. Minimize counts in descending rank order instead.
This permits the removal of a high-rank cell at the cost of
arbitrarily many lower-rank cells.
-/

/-- Finite lexicographic minimization, with the highest coordinate
most significant. No bound on the individual counts is needed. -/
theorem exists_descending_count_min {S : Type} (n : ℕ)
    (P : S → Prop) (count : S → ℕ → ℕ) (hex : ∃ s, P s) :
    ∃ s, P s ∧ ∀ t, P t → ∀ j < n,
      (∀ k, j < k → k < n → count s k = count t k) →
      count s j ≤ count t j := by
  classical
  induction n generalizing P with
  | zero =>
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, hs, fun _ _ _ hj _ => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := hex
    have he : ∃ m : ℕ, ∃ s, P s ∧ count s n = m :=
      ⟨count u n, u, hu, rfl⟩
    let d := Nat.find he
    obtain ⟨v,hv,hd⟩ := Nat.find_spec he
    have he' : ∃ s, P s ∧ count s n = d := ⟨v,hv,hd⟩
    obtain ⟨s,hs,hmin⟩ := ih (fun s => P s ∧ count s n = d) he'
    refine ⟨s, hs.1, ?_⟩
    intro t ht j hj habove
    by_cases hjn : j = n
    · subst j
      rw [hs.2]
      exact Nat.find_min' he ⟨t,ht,rfl⟩
    · have hjlt : j < n := by omega
      have htop := habove n hjlt (Nat.lt_succ_self n)
      have ht' : P t ∧ count t n = d := ⟨ht, htop.symm.trans hs.2⟩
      exact hmin t ht' j hjlt
        (fun k hjk hkn => habove k hjk (Nat.lt_succ_of_lt hkn))

/-- Count occurrences of a given rank, ignoring signs, heights and bases. -/
def rankCount {n : ℕ} (s : Peiffer.Sequence F (RankHeight n))
    (j : ℕ) : ℕ :=
  (s.filter (fun x => decide (x.1.2.1.val = j))).length

theorem rankCount_append {n : ℕ} (s t : Peiffer.Sequence F (RankHeight n))
    (j : ℕ) :
    rankCount (s ++ t) j = rankCount s j + rankCount t j := by
  simp only [rankCount, List.filter_append, List.length_append]

/-- The expression has lexicographically minimal descending rank
counts among all expressions of the same boundary element. -/
def RankMinimalExpression (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n)) : Prop :=
  Peiffer.evaluation (rankHeightRel pick X n) s = w ∧
  ∀ t : Peiffer.Sequence F (RankHeight n),
    Peiffer.evaluation (rankHeightRel pick X n) t = w →
    ∀ j < n, (∀ k, j < k → k < n → rankCount s k = rankCount t k) →
      rankCount s j ≤ rankCount t j

theorem exists_rankMinimalExpression (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      RankMinimalExpression pick X n w s := by
  obtain ⟨s,hs⟩ := exists_minimal_rankHeight_expression pick X n w hw
  exact exists_descending_count_min n
    (fun t : Peiffer.Sequence F (RankHeight n) =>
      Peiffer.evaluation (rankHeightRel pick X n) t = w)
    rankCount ⟨s,hs.1⟩

/-- A graded reduction may introduce arbitrarily many lower-rank
occurrences, but it must not change higher-rank counts. -/
theorem rankMinimal_block_no_reduction (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (p b r t : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ b ++ r))
    (he : Peiffer.evaluation (rankHeightRel pick X n) b =
      Peiffer.evaluation (rankHeightRel pick X n) t)
    (j : ℕ) (hj : j < n)
    (habove : ∀ k, j < k → k < n → rankCount b k = rankCount t k)
    (hstrict : rankCount t j < rankCount b j) : False := by
  have ht : Peiffer.evaluation (rankHeightRel pick X n) (p ++ t ++ r) = w := by
    rw [peiffer_evaluation_append, peiffer_evaluation_append, ← he]
    simpa only [peiffer_evaluation_append] using hs.1
  have hcounts : ∀ k, j < k → k < n →
      rankCount (p ++ b ++ r) k = rankCount (p ++ t ++ r) k := by
    intro k hjk hkn
    simp only [rankCount_append, habove k hjk hkn]
  have hle := hs.2 (p ++ t ++ r) ht j hj hcounts
  simp only [rankCount_append] at hle
  omega

/-- Replacing all negatively oriented occurrences by signed heights
preserves the entire rank profile, not just the total count. -/
theorem rankCount_positiveHeightOccurrence {n : ℕ}
    (s : Peiffer.Sequence F (RankHeight n)) (j : ℕ) :
    rankCount (s.map (positiveHeightOccurrence n)) j = rankCount s j := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have he : (positiveHeightOccurrence n x).1.2.1.val = x.1.2.1.val :=
      congrArg Fin.val (positiveHeightOccurrence_rank n x)
    unfold rankCount at ih ⊢
    simp only [List.map_cons, List.filter_cons, he]
    split <;> simp [ih]

theorem exists_positive_rankMinimalExpression (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      RankMinimalExpression pick X n w s ∧ ∀ x ∈ s, x.2 = true := by
  obtain ⟨s, hs⟩ := exists_rankMinimalExpression pick X n w hw
  refine ⟨s.map (positiveHeightOccurrence n), ⟨?_, ?_⟩, ?_⟩
  · rw [positiveHeightOccurrence_evaluation]
    exact hs.1
  · intro t ht j hj habove
    simp only [rankCount_positiveHeightOccurrence] at habove ⊢
    exact hs.2 t ht j hj habove
  · intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact positiveHeightOccurrence_sign n y

#print axioms exists_descending_count_min
#print axioms rankCount
#print axioms rankCount_append
#print axioms RankMinimalExpression
#print axioms exists_rankMinimalExpression
#print axioms rankMinimal_block_no_reduction
#print axioms rankCount_positiveHeightOccurrence
#print axioms exists_positive_rankMinimalExpression

end QuandleResearch.Issue070
