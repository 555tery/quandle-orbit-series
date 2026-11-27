import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SmallPresentation.SmallCancellationDipoleIdentityRibbon
import SmallPresentation.SmallCancellationGeometryIdentityPlanarity
import SmallPresentation.SmallCancellationGeometryIdentityVertexWords
import SmallPresentation.SmallCancellationGeometryBoundaryTheorem
import SmallPresentation.SmallCancellationGeometryRelativeRestriction
import SmallPresentation.SmallCancellationGeometryCorridorCuts
import SmallPresentation.SmallCancellationGeometryEdgeContractionTopology
import SmallPresentation.SmallCancellationGeometryRelativeRegions
import SmallPresentation.SmallCancellationGeometryRelativeRegionBoundary

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

open scoped BigOperators

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


/-! ## Lift lower-rank corrections into graded replacements

A replacement need only preserve the boundary modulo the lower-rank
normal subgroup. An actual expression for the discrepancy can then
be appended without increasing any count at or above the current
rank. This is the algebraic mechanism needed for a graded surgery.
-/

/-- Include a lower-rank occurrence in the larger rank interval. -/
def liftRankOccurrence {j n : ℕ} (hjn : j ≤ n)
    (x : Peiffer.Occurrence F (RankHeight j)) :
    Peiffer.Occurrence F (RankHeight n) :=
  ((x.1.1,(⟨x.1.2.1.val,lt_of_lt_of_le x.1.2.1.isLt hjn⟩,x.1.2.2)),x.2)

theorem liftRankOccurrence_term (pick : WeightedSelector)
    (X : ConjugatorChoice) {j n : ℕ} (hjn : j ≤ n)
    (x : Peiffer.Occurrence F (RankHeight j)) :
    Peiffer.term (rankHeightRel pick X n) (liftRankOccurrence hjn x) =
      Peiffer.term (rankHeightRel pick X j) x := by
  rfl

theorem liftRankOccurrence_evaluation (pick : WeightedSelector)
    (X : ConjugatorChoice) {j n : ℕ} (hjn : j ≤ n)
    (s : Peiffer.Sequence F (RankHeight j)) :
    Peiffer.evaluation (rankHeightRel pick X n) (s.map (liftRankOccurrence hjn)) =
      Peiffer.evaluation (rankHeightRel pick X j) s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change Peiffer.term (rankHeightRel pick X n) (liftRankOccurrence hjn x) *
        Peiffer.evaluation (rankHeightRel pick X n) (xs.map (liftRankOccurrence hjn)) =
      Peiffer.term (rankHeightRel pick X j) x *
        Peiffer.evaluation (rankHeightRel pick X j) xs
    rw [liftRankOccurrence_term, ih]

theorem rankCount_liftRankOccurrence_zero {j n : ℕ} (hjn : j ≤ n)
    (s : Peiffer.Sequence F (RankHeight j)) (k : ℕ) (hjk : j ≤ k) :
    rankCount (s.map (liftRankOccurrence hjn)) k = 0 := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have hne : (liftRankOccurrence hjn x).1.2.1.val ≠ k := by
      change x.1.2.1.val ≠ k
      exact ne_of_lt (lt_of_lt_of_le x.1.2.1.isLt hjk)
    unfold rankCount at ih ⊢
    simpa only [List.map_cons, List.filter_cons, hne, decide_false, Bool.false_eq_true,
      ite_false] using ih

/-- Every lower-stage kernel element can be filled using only
occurrences strictly below the specified rank. -/
theorem exists_lowerRank_filling (pick : WeightedSelector)
    (X : ConjugatorChoice) {j n : ℕ} (hjn : j ≤ n) (w : F)
    (hw : w ∈ weightedHeightStage pick X j) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      Peiffer.evaluation (rankHeightRel pick X n) s = w ∧
      ∀ k, j ≤ k → rankCount s k = 0 := by
  obtain ⟨s,hs⟩ := exists_minimal_rankHeight_expression pick X j w hw
  refine ⟨s.map (liftRankOccurrence hjn), ?_, ?_⟩
  · rw [liftRankOccurrence_evaluation]
    exact hs.1
  · intro k hk
    exact rankCount_liftRankOccurrence_zero hjn s k hk

/-- Graded reductions are impossible even when the proposed block
replacement agrees with the original block only modulo lower ranks.
The correction is explicitly filled by a finite lower-rank expression. -/
theorem rankMinimal_block_no_reduction_mod_lower (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (p b r t : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ b ++ r))
    (j : ℕ) (hj : j < n)
    (hmod : (Peiffer.evaluation (rankHeightRel pick X n) t)⁻¹ *
      Peiffer.evaluation (rankHeightRel pick X n) b ∈ weightedHeightStage pick X j)
    (habove : ∀ k, j < k → k < n → rankCount b k = rankCount t k)
    (hstrict : rankCount t j < rankCount b j) : False := by
  obtain ⟨q,hq,hzero⟩ := exists_lowerRank_filling pick X hj.le _ hmod
  have he : Peiffer.evaluation (rankHeightRel pick X n) b =
      Peiffer.evaluation (rankHeightRel pick X n) (t ++ q) := by
    rw [peiffer_evaluation_append, hq]
    group
  apply rankMinimal_block_no_reduction pick X n w p b r (t ++ q)
    hs he j hj
  · intro k hjk hkn
    rw [rankCount_append, hzero k hjk.le, add_zero]
    exact habove k hjk hkn
  · rw [rankCount_append, hzero j (le_refl j), add_zero]
    exact hstrict

/-- Choose an actual marked spherical ribbon from a positive,
rank-minimal expression, retaining its complete rank profile. -/
theorem exists_rankMinimal_ribbon_expression (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (hw : w ∈ weightedHeightStage pick X n) :
    ∃ s : Peiffer.Sequence F (RankHeight n),
      RankMinimalExpression pick X n w s ∧
      (∀ x ∈ s, x.2 = true) ∧
      ∃ he : Peiffer.evaluation (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w,
        (boundaryRibbon (rankHeightRows pick X n) w s he).EulerEquality := by
  obtain ⟨s,hs,hpos⟩ := exists_positive_rankMinimalExpression pick X n w hw
  have he : Peiffer.evaluation (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w := by
    simpa only [rankHeightRows_eval] using hs.1
  exact ⟨s,hs,hpos,he,boundaryRibbon_euler _ w s he⟩

#print axioms liftRankOccurrence
#print axioms liftRankOccurrence_term
#print axioms liftRankOccurrence_evaluation
#print axioms rankCount_liftRankOccurrence_zero
#print axioms exists_lowerRank_filling
#print axioms rankMinimal_block_no_reduction_mod_lower
#print axioms exists_rankMinimal_ribbon_expression


/-! ## Same-rank mergers modulo the earlier presentation

The connecting path can be trivial only modulo earlier ranks. Moving
the second occurrence across the intervening block and using the height
addition relation then gives a graded reduction, not necessarily an
exact two-to-one free-group identity.
-/

/-- Count a singleton without regard to its height, sign or base. -/
theorem rankCount_singleton {n : ℕ}
    (x : Peiffer.Occurrence F (RankHeight n)) (j : ℕ) :
    rankCount [x] j = if x.1.2.1.val = j then 1 else 0 := by
  by_cases h : x.1.2.1.val = j <;> simp [rankCount,h]

/-- The based merger condition is sufficient modulo the previous stage,
even for separated occurrences. The intervening block may have
arbitrary ranks; it is retained unchanged in the replacement. -/
theorem rankMinimal_no_separated_merge_mod_lower (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (w : F)
    (j : Fin n) (k l : ℤ) (u v : F)
    (p m r : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w
      (p ++ [((u,(j,k)),true)] ++ m ++ [((v,(j,l)),true)] ++ r))
    (hbase : (u*a^k)⁻¹ *
      (Peiffer.evaluation (rankHeightRel pick X n) m * v) ∈
        weightedHeightStage pick X j.val) : False := by
  let rel := rankHeightRel pick X n
  let b : Peiffer.Sequence F (RankHeight n) :=
    [((u,(j,k)),true)] ++ m ++ [((v,(j,l)),true)]
  let t : Peiffer.Sequence F (RankHeight n) :=
    [((u,(j,k+l)),true)] ++ m
  let N := weightedStages pick X j.val
  let : N.Normal := weightedStages_normal pick X j.val
  let q := QuotientGroup.mk' N
  have hb : (u*a^k)⁻¹ * (Peiffer.evaluation rel m * v) ∈ N := by
    simpa only [N, rel, weightedHeightStage_eq] using hbase
  have hq : q ((u*a^k)⁻¹ * (Peiffer.evaluation rel m * v)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hb
  simp only [map_mul, map_inv] at hq
  have hbaseq : q (Peiffer.evaluation rel m) * q v = q u * q (a^k) := by
    calc
      _ = (q u * q (a^k)) *
          ((q u * q (a^k))⁻¹ *
            (q (Peiffer.evaluation rel m) * q v)) := by group
      _ = _ := by rw [hq, mul_one]
  have hvq : q v =
      (q (Peiffer.evaluation rel m))⁻¹ * (q u * q (a^k)) := by
    calc
      _ = (q (Peiffer.evaluation rel m))⁻¹ *
          (q (Peiffer.evaluation rel m) * q v) := by group
      _ = _ := by rw [hbaseq]
  have he : q (Peiffer.evaluation rel b) = q (Peiffer.evaluation rel t) := by
    have hsingle (x : Peiffer.Occurrence F (RankHeight n)) :
        Peiffer.evaluation rel [x] = Peiffer.term rel x := by
      simp [Peiffer.evaluation]
    simp only [b,t,peiffer_evaluation_append,hsingle,Peiffer.term,Bool.cond_true]
    change q ((u * weightedRankHeightRelator pick X j.val k * u⁻¹) *
        Peiffer.evaluation rel m *
        (v * weightedRankHeightRelator pick X j.val l * v⁻¹)) =
      q ((u * weightedRankHeightRelator pick X j.val (k+l) * u⁻¹) *
        Peiffer.evaluation rel m)
    rw [weightedRankHeightRelator_add]
    simp only [map_mul,map_inv]
    rw [hvq]
    group
  have hmod : (Peiffer.evaluation rel t)⁻¹ *
      Peiffer.evaluation rel b ∈ weightedHeightStage pick X j.val := by
    rw [weightedHeightStage_eq]
    change (Peiffer.evaluation rel t)⁻¹ * Peiffer.evaluation rel b ∈ N
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((Peiffer.evaluation rel t)⁻¹ * Peiffer.evaluation rel b) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hsplit : RankMinimalExpression pick X n w (p ++ b ++ r) := by
    simpa only [b,List.append_assoc] using hs
  apply rankMinimal_block_no_reduction_mod_lower pick X n w p b r t
    hsplit j.val j.isLt hmod
  · intro d hd _
    simp only [b,t,rankCount_append,rankCount_singleton]
    simp [ne_of_lt hd]
  · simp only [b,t,rankCount_append,rankCount_singleton]
    simp

#print axioms rankCount_singleton
#print axioms rankMinimal_no_separated_merge_mod_lower


/-! ## Boundary of a lower-rank spherical region

Use the actual nonabelian boundary theorem of the ribbon library.
In particular, a region's boundary relation follows from its interior
cell labels and topology; it need not be assumed as an independent
algebraic relation. Cutting such a region out of a larger diagram
is a separate geometric construction.
-/

theorem signedLetterValue_reverse (x : Letter) :
    FreeGroup.mk [reverseLetter x] = (FreeGroup.mk [x])⁻¹ := by
  rcases x with ⟨i,s⟩
  cases s <;> rw [FreeGroup.inv_mk] <;> rfl

theorem rawWord_eval_prod (w : RawWord) :
    FreeGroup.mk w = (w.map (fun x => FreeGroup.mk [x])).prod := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change FreeGroup.mk ([x] ++ xs) =
      FreeGroup.mk [x] * (xs.map (fun x => FreeGroup.mk [x])).prod
    rw [← FreeGroup.mul_mk, ← ih]

/-- The quotient-valued nonabelian boundary theorem implies actual
normal-subgroup membership for the boundary word of a spherical
connected labelled region. -/
theorem ribbon_boundary_mem_normal {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hc : P.Connected) (hE : P.EulerEquality) (d : D)
    (hint : ∀ e, ¬ P.rotation.SameCycle d e →
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N) :
    FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N := by
  let q := QuotientGroup.mk' N
  have eval (ds : List D) :
      q (FreeGroup.mk (ds.map read)) =
        (ds.map (fun e => q (FreeGroup.mk [read e]))).prod := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons e es ih =>
      change q (FreeGroup.mk ([read e] ++ es.map read)) =
        q (FreeGroup.mk [read e]) *
          (es.map (fun e => q (FreeGroup.mk [read e]))).prod
      rw [← FreeGroup.mul_mk, map_mul, ih]
  have hprod := RibbonMap.boundary_product_one D P
    (fun e => q (FreeGroup.mk [read e])) (by
      intro e
      rw [he, signedLetterValue_reverse, map_inv])
    hc hE d (by
      intro e hne
      rw [← eval]
      exact (QuotientGroup.eq_one_iff _).mpr (hint e hne))
  apply (QuotientGroup.eq_one_iff _).mp
  change q (FreeGroup.mk ((P.vertexBoundary d).map read)) = 1
  rw [eval]
  exact hprod

/-- Cyclically cutting a relator does not alter membership in a normal
subgroup. The rotation is allowed even when its spelling is unreduced. -/
theorem rotated_word_mem_normal {N : Subgroup F} [N.Normal]
    (p r : RawWord) (h : FreeGroup.mk (p ++ r) ∈ N) :
    FreeGroup.mk (r ++ p) ∈ N := by
  have he : (FreeGroup.mk p)⁻¹ * FreeGroup.mk (p ++ r) *
      ((FreeGroup.mk p)⁻¹)⁻¹ = FreeGroup.mk (r ++ p) := by
    simp only [← FreeGroup.mul_mk]
    group
  rw [← he]
  exact (inferInstance : N.Normal).conj_mem _ h _

/-- Every cyclic reading of either orientation of a lower-rank
literal row is trivial in the preceding quotient. -/
theorem lowerRank_rotated_row_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ) (i : RankHeight j)
    (sign : Bool) (p r : RawWord)
    (hword : orientedWord (rankHeightRows pick X j i) sign = p ++ r) :
    FreeGroup.mk (r ++ p) ∈ weightedHeightStage pick X j := by
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  change FreeGroup.mk (r ++ p) ∈ N
  apply rotated_word_mem_normal p r
  rw [← hword]
  have hm : FreeGroup.mk (rankHeightRows pick X j i) ∈ N := by
    rw [rankHeightRows_eval]
    unfold N
    rw [← rankHeight_normalClosure]
    exact Subgroup.subset_normalClosure ⟨i,rfl⟩
  cases sign
  · change FreeGroup.mk (FreeGroup.invRev (rankHeightRows pick X j i)) ∈ N
    rw [← FreeGroup.inv_mk]
    exact N.inv_mem hm
  · exact hm

/-- A genuine connected spherical region over ranks below j has a
boundary trivial in stage j. The interior readings may start at
arbitrary cyclic corners and may use either orientation. -/
theorem lowerRank_region_boundary_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ) {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hc : P.Connected) (hE : P.EulerEquality) (d : D)
    (hint : ∀ e, ¬ P.rotation.SameCycle d e →
      ∃ (i : RankHeight j) (sign : Bool) (p r : RawWord),
        orientedWord (rankHeightRows pick X j i) sign = p ++ r ∧
        (P.vertexBoundary e).map read = r ++ p) :
    FreeGroup.mk ((P.vertexBoundary d).map read) ∈ weightedHeightStage pick X j := by
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  apply ribbon_boundary_mem_normal P read N he hc hE d
  intro e hne
  obtain ⟨i,sign,p,r,hw,hr⟩ := hint e hne
  rw [hr]
  exact lowerRank_rotated_row_mem pick X j i sign p r hw

#print axioms signedLetterValue_reverse
#print axioms rawWord_eval_prod
#print axioms ribbon_boundary_mem_normal
#print axioms rotated_word_mem_normal
#print axioms lowerRank_rotated_row_mem
#print axioms lowerRank_region_boundary_mem


/-- A lower-rank quadrilateral with an actual spherical realization
gives the connector-weight estimate on a minimal period. Its boundary
membership is derived from the interior rows, not postulated. -/
theorem activePeriod_region_quadrilateral_weight (pick : WeightedSelector)
    (i j : ℕ) (hji : j ≤ i)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (p v r u s t : RawWord)
    (hword : (pick (gubaState pick i).1 h).val.toWord = p ++ v ++ r)
    {D : Type} [Fintype D] (P : RibbonMap D) (read : D → Letter)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hc : P.Connected) (hE : P.EulerEquality) (d : D)
    (hint : ∀ e, ¬ P.rotation.SameCycle d e →
      ∃ (z : RankHeight j) (sign : Bool) (l q : RawWord),
        orientedWord (rankHeightRows pick (gubaConjugatorChoice pick) j z) sign = l ++ q ∧
        (P.vertexBoundary e).map read = q ++ l)
    (hboundary : (P.vertexBoundary d).map read =
      (v ++ t) ++ FreeGroup.invRev (s ++ u)) :
    rawWeight v ≤ rawWeight u + rawWeight s + rawWeight t := by
  have hb := lowerRank_region_boundary_mem pick (gubaConjugatorChoice pick) j
    P read he hc hE d hint
  rw [hboundary, weightedHeightStage_eq] at hb
  have hn := weightedStages_normal pick (gubaConjugatorChoice pick) i
  rw [← gubaState_stage pick i] at hn
  let : (gubaState pick i).1.Normal := hn
  apply minBad_factor_quadrilateral_weight
    (pick (gubaState pick i).1 h).property p v r u s t hword
  rw [gubaState_stage pick i]
  exact weightedStages_mono pick (gubaConjugatorChoice pick) hji hb

#print axioms activePeriod_region_quadrilateral_weight


/-! ## Restrict to the actual connected component

The restriction keeps the ordered boundary readings, not only the
number of vertices. Consequently the boundary theorem can be applied
to a component of a possibly disconnected spherical ribbon.
-/

theorem component_vertex_read {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a : D)
    (d : {d : D // P.SameComponent a d}) :
    ((P.componentRibbon a).vertexBoundary d).map (fun e => read e.val) =
      (P.vertexBoundary d.val).map read := by
  have hm := P.restrict_vertexBoundary (P.SameComponent a)
    (P.component_membership_edge a) (P.component_membership_rotation a) d
  change ((P.componentRibbon a).vertexBoundary d).map Subtype.val =
    P.vertexBoundary d.val at hm
  rw [← hm, List.map_map]
  rfl

theorem component_boundary_mem_normal {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hE : P.EulerEquality) (a : D)
    (hint : ∀ e, P.SameComponent a e → ¬P.rotation.SameCycle a e →
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N) :
    FreeGroup.mk ((P.vertexBoundary a).map read) ∈ N := by
  classical
  let d : {d : D // P.SameComponent a d} := ⟨a, Relation.EqvGen.refl a⟩
  have hE' : (P.componentRibbon a).EulerEquality := by
    change Fintype.card (P.componentRibbon a).Vertex +
      Fintype.card (P.componentRibbon a).Face =
      Fintype.card (P.componentRibbon a).Edge +
        2 * Fintype.card (P.componentRibbon a).Component
    rw [P.componentRibbon_card_components, mul_one]
    exact P.componentRibbon_sphere hE a
  have h := ribbon_boundary_mem_normal (P.componentRibbon a)
    (fun e => read e.val) N
    (fun e => he e.val) (P.componentRibbon_connected a) hE' d (by
      intro e hne
      rw [component_vertex_read]
      apply hint e.val e.property
      intro hh
      exact hne ((P.restrict_sameVertex_iff (P.SameComponent a)
        (P.component_membership_edge a) (P.component_membership_rotation a) d e).mpr hh))
  rw [component_vertex_read] at h
  exact h

/-- The actual boundary component preserves the entire marked word,
with its original orientation and chosen zero corner. -/
theorem boundaryComponent_read (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    ((boundaryComponent rows w s hs hw).vertexBoundary
      ⟨boundaryDart rows w s hw, Relation.EqvGen.refl _⟩).map
      (fun e => discRead (chosenSection (Fin 2)) (markedRows rows w)
        (boundaryIdentity s) e.val) = FreeGroup.invRev w.toWord := by
  rw [boundaryComponent, component_vertex_read]
  exact boundaryRibbon_read rows w s hs hw

#print axioms component_vertex_read
#print axioms component_boundary_mem_normal
#print axioms boundaryComponent_read


/-! ## Cutting a vertex along two actual intervals

A vertex cut switches the incoming arrows at two distinct corners.
The upstream theorem proves that it preserves spherical Euler equality.
The following lemmas retain the literal words and apply the boundary theorem
to a component separated by this actual permutation surgery.
-/

/-- An interval ending at the predecessor of the other cut corner
becomes a closed cycle, retaining its departure list in order. -/
theorem vertexCut_interval_read {D : Type} [Fintype D]
    (P : RibbonMap D) (a b c : D) (l : List D)
    (hw : SmallPresentationStatements.PermutationCycles.Walk P.rotation a c l)
    (hc : P.rotation c = b)
    (havoid : ∀ e ∈ l, P.rotation e ≠ a ∧ P.rotation e ≠ b)
    (hnd : (l ++ [c]).Nodup) :
    (P.vertexCut a b).vertexBoundary a = l ++ [c] := by
  classical
  have hw' : SmallPresentationStatements.PermutationCycles.Walk (P.vertexCut a b).rotation a c l := by
    apply hw.changePerm
    intro e he
    rw [P.vertexCut_rotation, SmallPresentationStatements.PermutationCycles.cutAt_apply]
    exact Equiv.swap_apply_of_ne_of_ne (havoid e he).1 (havoid e he).2
  have hlast : (P.vertexCut a b).rotation c = a := by
    rw [P.vertexCut_rotation, SmallPresentationStatements.PermutationCycles.cutAt_apply,
      hc, Equiv.swap_apply_right]
  have hclose : SmallPresentationStatements.PermutationCycles.Walk
      (P.vertexCut a b).rotation c a [c] := by
    apply SmallPresentationStatements.PermutationCycles.Walk.cons
    rw [hlast]
    exact SmallPresentationStatements.PermutationCycles.Walk.nil _
  have hcycle := (hw'.append hclose).eq_cycleBoundary (by simp) hnd
  exact hcycle.symm

theorem vertexCut_comm {D : Type} (P : RibbonMap D) (a b : D) :
    P.vertexCut a b = P.vertexCut b a := by
  classical
  apply RibbonMap.ext
  · rfl
  · simp only [RibbonMap.vertexCut_rotation,
      SmallPresentationStatements.PermutationCycles.cutAt, Equiv.swap_comm a b]

/-- If a cut separates its two new vertices into different components,
the part incident to the first corner has a boundary relation in N
whenever every other original vertex in that part reads a relation
in N. The complete old vertex is split into the two specified intervals. -/
theorem vertexCut_separated_boundary_mem {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (a b : D) (l r : List D)
    (hne : a ≠ b) (hsame : P.rotation.SameCycle a b)
    (hE : P.EulerEquality)
    (he : ∀ e, read (P.edge e) = reverseLetter (read e))
    (hold : P.vertexBoundary a = l ++ r)
    (hl : (P.vertexCut a b).vertexBoundary a = l)
    (hr : (P.vertexCut a b).vertexBoundary b = r)
    (hsep : ¬ (P.vertexCut a b).SameComponent a b)
    (hint : ∀ e, (P.vertexCut a b).SameComponent a e →
      ¬ P.rotation.SameCycle a e →
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N) :
    FreeGroup.mk (l.map read) ∈ N := by
  classical
  let S := P.vertexCut a b
  have hES : S.EulerEquality := P.vertexCut_preserves_euler a b hne hsame hE
  have hb := component_boundary_mem_normal S read N
    (fun e => he e) hES a (by
      intro e hcomp hnot
      have hnotold : ¬ P.rotation.SameCycle a e := by
        intro hh
        have hm := (P.mem_vertexBoundary_iff a e).mpr hh
        rw [hold, List.mem_append] at hm
        rcases hm with hm | hm
        · have hm' : e ∈ S.vertexBoundary a := by
            simpa only [S, hl] using hm
          exact hnot ((S.mem_vertexBoundary_iff a e).mp hm')
        · have hm' : e ∈ S.vertexBoundary b := by
            simpa only [S, hr] using hm
          have hbe := S.component_of_vertexCycle ((S.mem_vertexBoundary_iff b e).mp hm')
          exact hsep (Relation.EqvGen.trans _ _ _ hcomp
            (Relation.EqvGen.symm _ _ hbe))
      have hnotb : ¬ P.rotation.SameCycle e b := by
        intro hh
        exact hnotold (hsame.trans hh.symm)
      have hnot_a : ¬ P.rotation.SameCycle e a :=
        fun hh => hnotold hh.symm
      have hword : S.vertexBoundary e = P.vertexBoundary e :=
        SmallPresentationStatements.PermutationCycles.cycleBoundary_cutAt_unchanged
          P.rotation a b e hnot_a hnotb
      rw [hword]
      exact hint e hcomp hnotold)
  change FreeGroup.mk (((P.vertexCut a b).vertexBoundary a).map read) ∈ N at hb
  rw [hl] at hb
  exact hb

#print axioms vertexCut_interval_read
#print axioms vertexCut_comm
#print axioms vertexCut_separated_boundary_mem


/-! ## Join two boundary intervals after a sequence of cuts

Unlike a cut of a single vertex, this uses an actual joining edge
between two distinct boundary vertices of a refined ribbon. The
splicing operation retains the darts and preserves Euler equality.
The combined boundary is the literal concatenation of the two
based intervals. No spherical hypothesis on the refined or spliced
ribbon is required independently of the original ribbon.
-/

theorem edgeSplice_vertex_read {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a : D)
    (hn : ¬ P.rotation.SameCycle a (P.edge a)) :
    ((P.edgeSplice a).vertexBoundary (P.rotation a)).map read =
      (P.vertexBoundary (P.rotation a)).map read ++
        (P.vertexBoundary (P.edge a)).map read := by
  have hn' : ¬ P.rotation.SameCycle (P.rotation a) (P.edge a) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  have he := SmallPresentationStatements.PermutationCycles.cycleBoundary_cutAt_merge
    P.rotation (P.rotation a) (P.edge a) hn'
  change (P.edgeSplice a).vertexBoundary (P.rotation a) =
    P.vertexBoundary (P.rotation a) ++ P.vertexBoundary (P.edge a) at he
  rw [he, List.map_append]

/-- Two marked vertices joined by an edge can be treated as a single
exceptional boundary vertex in the nonabelian boundary theorem. -/
theorem edgeSplice_boundary_mem_normal {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (a : D) (hn : ¬P.rotation.SameCycle a (P.edge a))
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, P.SameComponent a d →
      ¬P.rotation.SameCycle a d →
      ¬P.rotation.SameCycle (P.edge a) d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N) :
    FreeGroup.mk ((P.vertexBoundary (P.rotation a)).map read ++
      (P.vertexBoundary (P.edge a)).map read) ∈ N := by
  classical
  let S := P.edgeSplice a
  have hES : S.EulerEquality := (P.edgeSplice_euler_iff a hn).mpr hE
  have hs := component_boundary_mem_normal S read N
    (fun d => he d) hES (P.rotation a) (by
      intro d hc hnot
      have ha : P.rotation.SameCycle (P.rotation a) a :=
        Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)
      have hn1 : ¬P.rotation.SameCycle a d := by
        intro hh
        exact hnot ((P.edgeSplice_sameVertex_iff a hn _ _).mpr (Or.inl (ha.trans hh)))
      have hn2 : ¬P.rotation.SameCycle (P.edge a) d := by
        intro hh
        exact hnot ((P.edgeSplice_sameVertex_iff a hn _ _).mpr
          (Or.inr ⟨Or.inl ha, Or.inr hh.symm⟩))
      have hsame : P.SameComponent a (P.rotation a) := P.component_rotation a
      have hce : P.SameComponent (P.rotation a) (P.edge a) :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hsame) (P.component_edge a)
      have hc' : P.SameComponent (P.rotation a) d :=
        P.vertexCut_component_refines (P.rotation a) (P.edge a) hce hc
      have hread : S.vertexBoundary d = P.vertexBoundary d :=
        SmallPresentationStatements.PermutationCycles.cycleBoundary_cutAt_unchanged
          P.rotation (P.rotation a) (P.edge a) d
          (fun hh => hn1 (ha.symm.trans hh.symm)) (fun hh => hn2 hh.symm)
      rw [hread]
      exact hint d (Relation.EqvGen.trans _ _ _ hsame hc') hn1 hn2)
  change FreeGroup.mk (((P.edgeSplice a).vertexBoundary (P.rotation a)).map read) ∈ N at hs
  rw [edgeSplice_vertex_read P read a hn] at hs
  exact hs

/-- A finite sequence of cuts of the original spherical diagram,
followed by splicing two distinct vertices along an actual edge,
supplies a boundary relation in the lower-rank presentation.
The interior readings are hypotheses about the actual resulting
component, not an independently postulated region. -/
theorem refined_two_boundary_region_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ) {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (tau : Equiv.Perm D)
    (href : SmallPresentationStatements.PermutationCycles.SplitRefinement P.rotation tau)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (a : D) (hn : ¬tau.SameCycle a (P.edge a))
    (hint : ∀ d, (P.withRotation tau).SameComponent a d →
      ¬tau.SameCycle a d → ¬tau.SameCycle (P.edge a) d →
      ∃ (i : RankHeight j) (sign : Bool) (l r : RawWord),
        orientedWord (rankHeightRows pick X j i) sign = l ++ r ∧
        ((P.withRotation tau).vertexBoundary d).map read = r ++ l) :
    FreeGroup.mk (((P.withRotation tau).vertexBoundary (tau a)).map read ++
      ((P.withRotation tau).vertexBoundary (P.edge a)).map read) ∈
        weightedHeightStage pick X j := by
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  have hE' : (P.withRotation tau).EulerEquality :=
    P.splitRefinement_preserves_euler href hE
  apply edgeSplice_boundary_mem_normal (P.withRotation tau) read N a hn hE' he
  intro d hc h1 h2
  obtain ⟨i,sign,l,r,hw,hr⟩ := hint d hc h1 h2
  rw [hr]
  exact lowerRank_rotated_row_mem pick X j i sign l r hw

#print axioms edgeSplice_vertex_read
#print axioms edgeSplice_boundary_mem_normal
#print axioms refined_two_boundary_region_mem


/-! ## Construct the two intervals from the actual cut

The two new boundary cycles concatenate to the old boundary, since
the inverse switch merges them back. In particular interval coverage
is a theorem, not an extra assumption on the operation.
-/

theorem vertexCut_partition {D : Type} [Fintype D]
    (P : RibbonMap D) (a b : D) (hne : a ≠ b)
    (hsame : P.rotation.SameCycle a b) :
    P.vertexBoundary a =
      (P.vertexCut a b).vertexBoundary a ++
        (P.vertexCut a b).vertexBoundary b := by
  have hsplit : ¬ (P.vertexCut a b).rotation.SameCycle a b :=
    SmallPresentationStatements.PermutationCycles.cutAt_not_sameCycle_of_sameCycle
      P.rotation a b hne hsame
  have hm := SmallPresentationStatements.PermutationCycles.cycleBoundary_cutAt_merge
    (P.vertexCut a b).rotation a b hsplit
  change ((P.vertexCut a b).vertexCut a b).vertexBoundary a =
    (P.vertexCut a b).vertexBoundary a ++ (P.vertexCut a b).vertexBoundary b at hm
  rw [P.vertexCut_twice] at hm
  exact hm

/-- A cut leaves the complete based traversal of a disjoint vertex unchanged. -/
theorem vertexCut_other_vertex_read {D : Type} [Fintype D]
    (P : RibbonMap D) (a b c : D)
    (ha : ¬ P.rotation.SameCycle c a)
    (hb : ¬ P.rotation.SameCycle c b) :
    (P.vertexCut a b).vertexBoundary c = P.vertexBoundary c :=
  SmallPresentationStatements.PermutationCycles.cycleBoundary_cutAt_unchanged
    P.rotation a b c ha hb

/-- For two original distinct vertices, cutting each at two actual
corners gives a genuine split refinement of the original diagram.
Both literal partitions are retained, including the first after
the second cut. -/
theorem exists_two_vertex_cut_refinement {D : Type} [Fintype D]
    (P : RibbonMap D) (a b c d : D)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : P.rotation.SameCycle a b)
    (h2 : P.rotation.SameCycle c d)
    (hdisj : ¬ P.rotation.SameCycle a c) :
    ∃ tau : Equiv.Perm D,
      SmallPresentationStatements.PermutationCycles.SplitRefinement P.rotation tau ∧
      P.vertexBoundary a = (P.withRotation tau).vertexBoundary a ++
        (P.withRotation tau).vertexBoundary b ∧
      P.vertexBoundary c = (P.withRotation tau).vertexBoundary c ++
        (P.withRotation tau).vertexBoundary d ∧
      ¬ tau.SameCycle a c := by
  let S := P.vertexCut a b
  have hca : ¬ P.rotation.SameCycle c a := fun h => hdisj h.symm
  have hcb : ¬ P.rotation.SameCycle c b := fun h => hdisj (h1.trans h.symm)
  have hcread : S.vertexBoundary c = P.vertexBoundary c :=
    vertexCut_other_vertex_read P a b c hca hcb
  have h2' : S.rotation.SameCycle c d := by
    apply (S.mem_vertexBoundary_iff c d).mp
    rw [hcread]
    exact (P.mem_vertexBoundary_iff c d).mpr h2
  have hca' : ¬ S.rotation.SameCycle c a := by
    intro h
    have hm := (S.mem_vertexBoundary_iff c a).mpr h
    rw [hcread] at hm
    exact hca ((P.mem_vertexBoundary_iff c a).mp hm)
  have hcb' : ¬ S.rotation.SameCycle c b := by
    intro h
    have hm := (S.mem_vertexBoundary_iff c b).mpr h
    rw [hcread] at hm
    exact hcb ((P.mem_vertexBoundary_iff c b).mp hm)
  let T := S.vertexCut c d
  have haread : T.vertexBoundary a = S.vertexBoundary a :=
    vertexCut_other_vertex_read S c d a
      (fun h => hca' h.symm) (fun h => hca' (h2'.trans h.symm))
  have hbread : T.vertexBoundary b = S.vertexBoundary b :=
    vertexCut_other_vertex_read S c d b
      (fun h => hcb' h.symm) (fun h => hcb' (h2'.trans h.symm))
  have hpart1 := vertexCut_partition P a b hab h1
  have hpart2 := vertexCut_partition S c d hcd h2'
  have href : SmallPresentationStatements.PermutationCycles.SplitRefinement
      P.rotation T.rotation :=
    SmallPresentationStatements.PermutationCycles.SplitRefinement.cut
      (SmallPresentationStatements.PermutationCycles.SplitRefinement.single
        P.rotation a b hab h1) c d hcd h2'
  refine ⟨T.rotation, href, ?_, ?_, ?_⟩
  · change P.vertexBoundary a = T.vertexBoundary a ++ T.vertexBoundary b
    rw [haread, hbread]
    exact hpart1
  · change P.vertexBoundary c = T.vertexBoundary c ++ T.vertexBoundary d
    rw [← hcread]
    exact hpart2
  · intro h
    have hm := (T.mem_vertexBoundary_iff a c).mpr h
    rw [haread] at hm
    exact hca' ((S.mem_vertexBoundary_iff a c).mp hm).symm

#print axioms vertexCut_partition
#print axioms vertexCut_other_vertex_read
#print axioms exists_two_vertex_cut_refinement


/-- Cutting after a prescribed positive number k+1 of darts, strictly
shorter than the full cycle, isolates exactly those first k+1 darts.
The distinctness and no-premature-return hypotheses are derived from
the minimal period of the rotation. -/
theorem vertexCut_prescribed_interval {D : Type} [Fintype D]
    (P : RibbonMap D) (a : D) (k : ℕ)
    (hk : k + 1 < Function.minimalPeriod P.rotation a) :
    (P.vertexCut a (P.rotation^[k+1] a)).vertexBoundary a =
      List.ofFn (fun i : Fin k => P.rotation^[i.val] a) ++
        [P.rotation^[k] a] := by
  classical
  let c := P.rotation^[k] a
  let b := P.rotation^[k+1] a
  let l := List.ofFn (fun i : Fin k => P.rotation^[i.val] a)
  have hw : SmallPresentationStatements.PermutationCycles.Walk
      P.rotation a c l :=
    SmallPresentationStatements.PermutationCycles.Walk.of_iterate P.rotation k a
  have hc : P.rotation c = b := by
    dsimp only [c,b]
    rw [Function.iterate_succ_apply']
  have hinj : ∀ i j : ℕ, i < Function.minimalPeriod P.rotation a →
      j < Function.minimalPeriod P.rotation a →
      P.rotation^[i] a = P.rotation^[j] a → i = j := by
    intro i j hi hj he
    exact Function.iterate_injOn_Iio_minimalPeriod hi hj he
  have hav : ∀ e ∈ l, P.rotation e ≠ a ∧ P.rotation e ≠ b := by
    intro e he
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
    rw [← hi]
    constructor
    · intro hh
      have hh' : P.rotation^[i.val+1] a = P.rotation^[0] a := by
        rw [Function.iterate_succ_apply', Function.iterate_zero_apply]
        exact hh
      have h := hinj (i.val+1) 0 (by omega) (by omega) hh'
      omega
    · intro hh
      have hh' : P.rotation^[i.val+1] a = P.rotation^[k+1] a := by
        rw [Function.iterate_succ_apply']
        exact hh
      have h := hinj (i.val+1) (k+1) (by omega) hk hh'
      omega
  have hnd : (l ++ [c]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · apply List.nodup_ofFn.mpr
      intro i j he
      apply Fin.ext
      exact hinj i.val j.val (by omega) (by omega) he
    · intro e he z hz hez
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
      have hzc : z = c := List.mem_singleton.mp hz
      have hh : P.rotation^[i.val] a = P.rotation^[k] a :=
        hi.trans (hez.trans hzc)
      have h := hinj i.val k (by omega) (by omega) hh
      omega
  exact vertexCut_interval_read P a b c l hw hc hav hnd

#print axioms vertexCut_prescribed_interval


/-! ## Read the actual rank labels at arbitrary corners

For a region inside the original marked ribbon, the interior
relation should be deduced from the original occurrence label.
There is no need to supply a fresh cyclic spelling of each row.
-/

/-- Moving the basepoint of a vertex does not change membership of
its evaluated reading in a normal subgroup. -/
theorem ribbon_vertex_mem_sameCycle {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (d e : D) (h : P.rotation.SameCycle d e) :
    FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N ↔
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N := by
  let q := QuotientGroup.mk' N
  have eval (ds : List D) :
      q (FreeGroup.mk (ds.map read)) =
        (ds.map (fun x => q (FreeGroup.mk [read x]))).prod := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons x xs ih =>
      change q (FreeGroup.mk ([read x] ++ xs.map read)) =
        q (FreeGroup.mk [read x]) *
          (xs.map (fun z => q (FreeGroup.mk [read z]))).prod
      rw [← FreeGroup.mul_mk, map_mul, ih]
  have hc := SmallPresentationStatements.PermutationCycles.cycleProduct_eq_one_of_sameCycle
    P.rotation (fun x => q (FreeGroup.mk [read x])) h
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff]
  change (q (FreeGroup.mk ((P.vertexBoundary d).map read)) = 1 ↔
    q (FreeGroup.mk ((P.vertexBoundary e).map read)) = 1)
  rw [eval, eval]
  exact hc

/-- The complete reading at any corner of an actual labelled disc
belongs to N as soon as its original row evaluates into N. -/
theorem boundaryRibbon_vertex_mem_of_label (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (N : Subgroup F) [N.Normal]
    (d : DiscDarts (markedRows rows w) (boundaryIdentity s)) (i : I)
    (hi : (boundaryIdentity s)[discOccurrence (markedRows rows w)
      (boundaryIdentity s) d].1.2 = some i)
    (hm : FreeGroup.mk (rows i) ∈ N) :
    FreeGroup.mk (((boundaryRibbon rows w s hs).vertexBoundary d).map
      (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) ∈ N := by
  obtain ⟨idx,k,rfl⟩ := exists_discAt (markedRows rows w) (boundaryIdentity s) d
  have hi' : (boundaryIdentity s)[idx].1.2 = some i := by
    simpa only [discOccurrence_at] using hi
  let z := discAt (markedRows rows w) (boundaryIdentity s) idx
    ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  have hz : (boundaryRibbon rows w s hs).rotation.SameCycle z
      (discAt (markedRows rows w) (boundaryIdentity s) idx k) := by
    change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle z _
    rw [disc_sameCycle_iff]
    simp only [z, discOccurrence_at]
  apply (ribbon_vertex_mem_sameCycle (boundaryRibbon rows w s hs)
    (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))
    N z _ hz).mp
  change FreeGroup.mk (((boundaryRibbon rows w s hs).vertexBoundary
    (discAt (markedRows rows w) (boundaryIdentity s) idx
      ⟨0, Nat.zero_lt_of_lt k.isLt⟩)).map
      (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) ∈ N
  rw [boundaryRibbon_interior_read rows w s hs idx i hi' (Nat.zero_lt_of_lt k.isLt)]
  cases (boundaryIdentity s)[idx].2
  · change FreeGroup.mk (FreeGroup.invRev (rows i)) ∈ N
    rw [← FreeGroup.inv_mk]
    exact N.inv_mem hm
  · exact hm

/-- A lower-rank label alone suffices for membership of the actual
vertex reading in the preceding stage, regardless of its corner. -/
theorem rankRibbon_lower_vertex_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (d : DiscDarts (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s))
    (i : RankHeight n)
    (hi : (boundaryIdentity s)[discOccurrence
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s) d].1.2 = some i)
    (hlt : i.1.val < j) :
    FreeGroup.mk (((boundaryRibbon (rankHeightRows pick X n) w s hs).vertexBoundary d).map
      (discRead (chosenSection (Fin 2)) (markedRows (rankHeightRows pick X n) w)
        (boundaryIdentity s))) ∈ weightedHeightStage pick X j := by
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  apply boundaryRibbon_vertex_mem_of_label (rankHeightRows pick X n)
    w s hs N d i hi
  rw [rankHeightRows_eval]
  change weightedRankHeightRelator pick X i.1.val i.2 ∈ N
  unfold N
  rw [← rankHeight_normalClosure]
  exact Subgroup.subset_normalClosure ⟨(⟨i.1.val,hlt⟩,i.2),rfl⟩

/-- Rotation agreement on the original complete vertex is enough
to preserve its exact based reading in any refined ribbon. -/
theorem refined_vertex_read_of_agreement {D : Type} [Fintype D]
    (P : RibbonMap D) (tau : Equiv.Perm D) (d : D)
    (h : ∀ e, P.rotation.SameCycle d e → tau e = P.rotation e) :
    (P.withRotation tau).vertexBoundary d = P.vertexBoundary d := by
  have hw := SmallPresentationStatements.PermutationCycles.cycleBoundary_walk P.rotation d
  have hw' : SmallPresentationStatements.PermutationCycles.Walk tau d d
      (P.vertexBoundary d) := by
    apply hw.changePerm
    intro e he
    exact h e ((P.mem_vertexBoundary_iff d e).mp he)
  exact (hw'.eq_cycleBoundary
    (SmallPresentationStatements.PermutationCycles.cycleBoundary_ne_nil P.rotation d)
    (SmallPresentationStatements.PermutationCycles.cycleBoundary_nodup P.rotation d)).symm

#print axioms ribbon_vertex_mem_sameCycle
#print axioms boundaryRibbon_vertex_mem_of_label
#print axioms rankRibbon_lower_vertex_mem
#print axioms refined_vertex_read_of_agreement


/-- The actual refined rank ribbon supplies all interior relations
from its original labels. Only rank bounds and preservation of the
lower-rank rotations are required, not a separate word-reading
certificate at every interior corner. -/
theorem rankRibbon_refined_two_boundary_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (tau : Equiv.Perm
      (DiscDarts (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s))) :
    let P := boundaryRibbon (rankHeightRows pick X n) w s hs
    let read := discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
    ∀ (a : DiscDarts (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)),
      SmallPresentationStatements.PermutationCycles.SplitRefinement P.rotation tau →
      (¬tau.SameCycle a (P.edge a)) →
      (∀ d, (P.withRotation tau).SameComponent a d →
        ¬tau.SameCycle a d → ¬tau.SameCycle (P.edge a) d →
        (∃ i : RankHeight n,
          (boundaryIdentity s)[discOccurrence
            (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s) d].1.2 =
              some i ∧ i.1.val < j) ∧
        (∀ e, P.rotation.SameCycle d e → tau e = P.rotation e)) →
      FreeGroup.mk (((P.withRotation tau).vertexBoundary (tau a)).map read ++
        ((P.withRotation tau).vertexBoundary (P.edge a)).map read) ∈
        weightedHeightStage pick X j := by
  intro P read a href hn hint
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  have hE : P.EulerEquality := boundaryRibbon_euler _ w s hs
  have hE' : (P.withRotation tau).EulerEquality :=
    P.splitRefinement_preserves_euler href hE
  have he : ∀ d, read (P.edge d) = reverseLetter (read d) :=
    relatorRibbon_edge_read (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
      (boundaryIdentity_evaluation _ w s hs)
  apply edgeSplice_boundary_mem_normal (P.withRotation tau) read N a hn hE' he
  intro d hc h1 h2
  obtain ⟨⟨i,hi,hlt⟩,hag⟩ := hint d hc h1 h2
  rw [refined_vertex_read_of_agreement P tau d hag]
  exact rankRibbon_lower_vertex_mem pick X n j w s hs d i hi hlt

#print axioms rankRibbon_refined_two_boundary_mem


/-! ## Cut only vertices above the chosen rank

A predicate on whole original vertices can be protected while
performing cuts. In particular all lower-rank rows remain intact,
even when the higher-rank boundary intervals are subdivided.
-/

theorem vertexCut_rotation_eq_on_protected {D : Type}
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (a b d : D) (ha : ¬keep a) (hb : ¬keep b) (hd : keep d) :
    (P.vertexCut a b).rotation d = P.rotation d := by
  classical
  rw [P.vertexCut_rotation, SmallPresentationStatements.PermutationCycles.cutAt_apply]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact ha (h ▸ (hkeep d).mpr hd)
  · intro h
    exact hb (h ▸ (hkeep d).mpr hd)

theorem vertexCut_protected_invariant {D : Type}
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (a b : D) (ha : ¬keep a) (hb : ¬keep b) :
    ∀ d, keep ((P.vertexCut a b).rotation d) ↔ keep d := by
  classical
  intro d
  by_cases hd : keep d
  · rw [vertexCut_rotation_eq_on_protected P keep hkeep a b d ha hb hd]
    exact hkeep d
  · have hnot : ¬keep (P.rotation d) := fun h => hd ((hkeep d).mp h)
    rw [P.vertexCut_rotation, SmallPresentationStatements.PermutationCycles.cutAt_apply]
    by_cases h1 : P.rotation d = a
    · rw [h1, Equiv.swap_apply_left]
      exact iff_of_false hb hd
    · by_cases h2 : P.rotation d = b
      · rw [h2, Equiv.swap_apply_right]
        exact iff_of_false ha hd
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact hkeep d

/-- A genuine sequence of cuts outside protected vertices retains
their original rotations and keeps the protection predicate invariant. -/
theorem protected_splitRefinement_agreement {D : Type}
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (cuts : List (D × D))
    (hout : ∀ x ∈ cuts, ¬keep x.1 ∧ ¬keep x.2) :
    let S := cuts.foldl (fun (Q : RibbonMap D) x => Q.vertexCut x.1 x.2) P
    (∀ d, keep (S.rotation d) ↔ keep d) ∧
      (∀ d, keep d → S.rotation d = P.rotation d) := by
  induction cuts generalizing P with
  | nil => exact ⟨hkeep, fun _ _ => rfl⟩
  | cons x xs ih =>
    have hx := hout x (by simp)
    let Q := P.vertexCut x.1 x.2
    have hQ := vertexCut_protected_invariant P keep hkeep x.1 x.2 hx.1 hx.2
    have hrest := ih Q hQ (fun y hy => hout y (List.mem_cons_of_mem _ hy))
    refine ⟨hrest.1, ?_⟩
    intro d hd
    exact (hrest.2 d hd).trans
      (vertexCut_rotation_eq_on_protected P keep hkeep x.1 x.2 d hx.1 hx.2 hd)

/-- Protection defined by actual lower-rank occurrence labels is
constant around each original vertex, including the marked boundary. -/
def lowerRankDart (pick : WeightedSelector) (X : ConjugatorChoice)
    (n j : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (d : DiscDarts (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)) : Prop :=
  ∃ i : RankHeight n,
    (boundaryIdentity s)[discOccurrence
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s) d].1.2 =
        some i ∧ i.1.val < j

theorem lowerRankDart_sameCycle (pick : WeightedSelector) (X : ConjugatorChoice)
    (n j : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (d e : DiscDarts (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s))
    (h : (boundaryRibbon (rankHeightRows pick X n) w s hs).rotation.SameCycle d e) :
    lowerRankDart pick X n j w s d ↔ lowerRankDart pick X n j w s e := by
  change (discRotation (markedRows (rankHeightRows pick X n) w)
    (boundaryIdentity s)).SameCycle d e at h
  rw [disc_sameCycle_iff] at h
  unfold lowerRankDart
  simp only [h]

#print axioms vertexCut_rotation_eq_on_protected
#print axioms vertexCut_protected_invariant
#print axioms protected_splitRefinement_agreement
#print axioms lowerRankDart
#print axioms lowerRankDart_sameCycle


/-- In the actual rank ribbon, cutting only at non-lower-rank darts
automatically preserves every lower-rank row. Thus the region lemma
requires only the rank bound on its interior, not a second rotation
agreement hypothesis. -/
theorem rankRibbon_protected_cuts_boundary_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (cuts : List ((DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s)) × (DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s)))) :
    let P := boundaryRibbon (rankHeightRows pick X n) w s hs
    let keep := lowerRankDart pick X n j w s
    let S := cuts.foldl (fun Q x => Q.vertexCut x.1 x.2) P
    let read := discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
    ∀ a, (∀ x ∈ cuts, ¬keep x.1 ∧ ¬keep x.2) →
      SmallPresentationStatements.PermutationCycles.SplitRefinement P.rotation S.rotation →
      (¬ S.rotation.SameCycle a (P.edge a)) →
      (∀ d, (P.withRotation S.rotation).SameComponent a d →
        ¬ S.rotation.SameCycle a d →
        ¬ S.rotation.SameCycle (P.edge a) d → keep d) →
      FreeGroup.mk (((P.withRotation S.rotation).vertexBoundary (S.rotation a)).map read ++
        ((P.withRotation S.rotation).vertexBoundary (P.edge a)).map read) ∈
        weightedHeightStage pick X j := by
  intro P keep S read a hout href hn hint
  have hkeep : ∀ d, keep (P.rotation d) ↔ keep d := by
    intro d
    exact lowerRankDart_sameCycle pick X n j w s hs (P.rotation d) d
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  have hag := (protected_splitRefinement_agreement P keep hkeep cuts hout).2
  apply rankRibbon_refined_two_boundary_mem pick X n j w s hs S.rotation a href hn
  intro d hc hd1 hd2
  have hd := hint d hc hd1 hd2
  refine ⟨hd, ?_⟩
  intro e he
  exact hag e ((lowerRankDart_sameCycle pick X n j w s hs d e he).mp hd)

#print axioms rankRibbon_protected_cuts_boundary_mem


/-! ## Canonical lower-rank regions have no isolated single outlet

Split every vertex not below the threshold into single darts. This
is the coefficientRegions construction, an actual finite refinement
of the given ribbon. If a component meets just one such dart, its
letter is forced to vanish in the lower-stage quotient. Consequently
under the rank-induction nonvanishing hypothesis every exposed dart
has another exposed dart in its component.
-/

theorem fixed_vertex_read_singleton {D : Type} [Fintype D]
    (P : RibbonMap D) (a : D) (ha : P.rotation a = a) :
    P.vertexBoundary a = [a] := by
  have hw : SmallPresentationStatements.PermutationCycles.Walk P.rotation a a [a] := by
    apply SmallPresentationStatements.PermutationCycles.Walk.cons
    rw [ha]
    exact SmallPresentationStatements.PermutationCycles.Walk.nil _
  exact (hw.eq_cycleBoundary (by simp) (by simp)).symm

theorem coefficientRegions_no_unique_outlet {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a : D) (ha : ¬keep a) (hna : FreeGroup.mk [read a] ∉ N) :
    ∃ b, (P.coefficientRegions keep hkeep).SameComponent a b ∧
      ¬keep b ∧ b ≠ a := by
  classical
  let S := P.coefficientRegions keep hkeep
  have hS : S.EulerEquality := P.coefficientRegions_euler keep hkeep hE
  have hfix : S.rotation a = a := by
    simp [S, RibbonMap.coefficientRegions_rotation, ha]
  have hread := fixed_vertex_read_singleton S a hfix
  by_contra hnone
  have hm := component_boundary_mem_normal S read N (fun d => he d) hS a (by
    intro d hc hnc
    have hd : keep d := by
      by_contra hd
      have hne : d ≠ a := by
        intro h
        subst d
        exact hnc (.refl _ _)
      exact hnone ⟨d,hc,hd,hne⟩
    have hag : ∀ e, P.rotation.SameCycle d e → S.rotation e = P.rotation e := by
      intro e hde
      have hk : keep e := by
        obtain ⟨m, hm⟩ := hde.exists_nat_pow_eq
        rw [← hm]
        clear hm hde
        induction m with
        | zero => exact hd
        | succ m ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact (hkeep _).mpr ih
      simp [S, RibbonMap.coefficientRegions_rotation, hk]
    change FreeGroup.mk (((P.withRotation S.rotation).vertexBoundary d).map read) ∈ N
    rw [refined_vertex_read_of_agreement P S.rotation d hag]
    exact hint d hd)
  rw [hread] at hm
  exact hna (by simpa only [List.map_cons, List.map_nil] using hm)

/-- Canonical decomposition at rank j. Every incidence of a higher
rank or the original boundary is an outlet. The nonvanishing
condition on its letter is the only algebraic hypothesis here. -/
theorem rankRibbon_lower_regions_no_unique_outlet (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w) :
    let P := boundaryRibbon (rankHeightRows pick X n) w s hs
    let keep := lowerRankDart pick X n j w s
    let read := discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
    ∃ hkeep : ∀ d, keep (P.rotation d) ↔ keep d,
      ∀ a, ¬keep a → FreeGroup.mk [read a] ∉ weightedHeightStage pick X j →
        ∃ b, (P.coefficientRegions keep hkeep).SameComponent a b ∧
          ¬keep b ∧ b ≠ a := by
  intro P keep read
  have hkeep : ∀ d, keep (P.rotation d) ↔ keep d := by
    intro d
    exact lowerRankDart_sameCycle pick X n j w s hs (P.rotation d) d
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  refine ⟨hkeep, ?_⟩
  intro a ha hna
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  apply coefficientRegions_no_unique_outlet P read N keep hkeep
    (boundaryRibbon_euler _ w s hs)
  · exact relatorRibbon_edge_read (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
      (boundaryIdentity_evaluation _ w s hs)
  · intro d hd
    obtain ⟨i,hi,hlt⟩ := hd
    exact rankRibbon_lower_vertex_mem pick X n j w s hs d i hi hlt
  · exact ha
  · exact hna

#print axioms fixed_vertex_read_singleton
#print axioms coefficientRegions_no_unique_outlet
#print axioms rankRibbon_lower_regions_no_unique_outlet


/-! ## Guba, Lemma 23 (pp. 258–259): quantitative conclusion

The original proof removes a cell of rank >= 2, applies the coverage
of Lemma 22 to the resulting annulus, discards internal contiguities,
and applies Lemma 21 to the remaining arcs. We record its precise
numerical implication, separately from those geometric obligations.
All weights here are scaled by 10^80 as in Words.lean.
-/

/-- The a-section takes at most the fraction lambda of the perimeter.
This is the actual four-block row, not an arbitrary cell weight. -/
theorem guba23_firstKind_weight (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n)
    (h : ∃ w : F, ¬ Good (gubaState pick i.1.val).1 w)
    (hk : i.2 ≠ 0) :
    let P := rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i)
    let D := 2 * positiveWeight (activeLongWord pick i.1.val h) +
      i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val
    P = D + i.2.natAbs ∧
      10^80 * i.2.natAbs ≤ P := by
  dsimp
  have hp := guba_rankHeightRows_weight pick n i h hk
  have hc := weight_ge_of_bad (gubaState pick i.1.val).1
    (pick (gubaState pick i.1.val).1 h).val
    (pick (gubaState pick i.1.val).1 h).property.1
  have hm := Nat.mul_le_mul_left i.2.natAbs hc
  rw [hp]
  constructor
  · rfl
  · have hm' : (10^80 : ℕ) * i.2.natAbs ≤
        i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val :=
      (Nat.mul_comm _ _).le.trans hm
    omega

/-- The final estimate of Lemma 23, with the paper's actual constants:
rho=.9, eta=.95, T=10^11, lambda=10^-80, gamma=10^-19.
C is the total retained length of the interior-cell contiguity arcs.
The coverage and transfer assumptions are precisely the geometric
part that still has to be proved. -/
theorem guba23_perimeter_arithmetic (P D C B : ℚ)
    (hP : 0 < P)
    (hD : (1 - 1 / 10^80) * P ≤ D)
    (hcover : (95/100 - 18/10^11) * D < C)
    (htransfer : (9/10) * C - (6/10^19) * P ≤ B) :
    (4/5) * P < B := by
  norm_num at hD hcover htransfer ⊢
  linarith

/-- A concrete rank-height row satisfies the perimeter conclusion
once the annular coverage and transfer bounds of Lemma 23 are
established for that row. This does NOT assert their existence. -/
theorem guba23_row_perimeter_of_coverage (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n) (w : F)
    (h : ∃ u : F, ¬ Good (gubaState pick i.1.val).1 u)
    (hk : i.2 ≠ 0) (C : ℚ)
    (hcover : (95/100 - 18/10^11) *
      ((2 * positiveWeight (activeLongWord pick i.1.val h) +
        i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val : ℕ) : ℚ) < C)
    (htransfer : (9/10) * C - (6/10^19) *
      (rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) : ℚ) ≤
        (weightedLength w : ℚ)) :
    4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) <
      5 * weightedLength w := by
  let P := rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i)
  let D := 2 * positiveWeight (activeLongWord pick i.1.val h) +
    i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val
  obtain ⟨hp,hm⟩ := guba23_firstKind_weight pick n i h hk
  change P = D + i.2.natAbs at hp
  change 10^80 * i.2.natAbs ≤ P at hm
  have hkn : 0 < i.2.natAbs := Int.natAbs_pos.mpr hk
  have hp0 : 0 < P := by omega
  have hpQ : 0 < (P : ℚ) := by exact_mod_cast hp0
  have hpQ' : (P : ℚ) = (D : ℚ) + (i.2.natAbs : ℚ) := by exact_mod_cast hp
  have hmQ : (10 : ℚ)^80 * (i.2.natAbs : ℚ) ≤ (P : ℚ) := by exact_mod_cast hm
  have hd : (1 - 1 / 10^80) * (P : ℚ) ≤ (D : ℚ) := by
    norm_num at hpQ' hmQ ⊢
    linarith only [hpQ', hmQ]
  have hres := guba23_perimeter_arithmetic (P : ℚ) (D : ℚ) C
    (weightedLength w : ℚ) hpQ hd hcover htransfer
  have hnat : (4 : ℚ) * (P : ℚ) < 5 * (weightedLength w : ℚ) := by linarith
  exact_mod_cast hnat

#print axioms guba23_firstKind_weight
#print axioms guba23_perimeter_arithmetic
#print axioms guba23_row_perimeter_of_coverage



/-! ## Lemma 23: additivity and disjoint outer arc accounting

The geometric input is a system of contiguity arcs. Here we make the
summation step explicit on their literal word readings. The sublist
condition is a sufficient certificate of disjoint outer arcs in
boundary order (with a suitable choice of cut). No existence of such
a system or per-arc geometric estimate is asserted.
-/

theorem guba23_sublist_weight {u v : RawWord} (h : u.Sublist v) :
    rawWeight u ≤ rawWeight v := by
  induction h <;> simp_all [rawWeight]
  omega

theorem guba23_flatMap_weight {A : Type} (xs : List A) (f : A → RawWord) :
    rawWeight (xs.flatMap f) = (xs.map (fun x => rawWeight (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, rawWeight_append, List.map_cons, List.sum_cons, ih]

/-- Outer arc readings can be counted only once: their concatenation
must occur as a sublist of the actual boundary reading. -/
theorem guba23_outer_arcs_weight (arcs : List (RawWord × RawWord)) (v : RawWord)
    (h : (arcs.flatMap Prod.snd).Sublist v) :
    (arcs.map (fun q => rawWeight q.2)).sum ≤ rawWeight v := by
  rw [← guba23_flatMap_weight arcs Prod.snd]
  exact guba23_sublist_weight h

/-- Summing Lemma 21's local estimates, including one error term per arc. -/
theorem guba23_arc_transfer_sum (arcs : List (RawWord × RawWord)) (P : ℚ)
    (hlocal : ∀ q ∈ arcs,
      (9/10 : ℚ) * (rawWeight q.1 : ℚ) - (2/10^19 : ℚ) * P ≤
        (rawWeight q.2 : ℚ)) :
    (9/10 : ℚ) * ((arcs.map (fun q => rawWeight q.1)).sum : ℚ) -
      (arcs.length : ℚ) * ((2/10^19 : ℚ) * P) ≤
      ((arcs.map (fun q => rawWeight q.2)).sum : ℚ) := by
  induction arcs with
  | nil => simp
  | cons q qs ih =>
    have hq := hlocal q (by simp)
    have ht := ih (fun p hp => hlocal p (by simp [hp]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith only [hq, ht]

/-- The actual signed boundary word bounds the transferred lengths.
The at-most-three condition and the sublist certificate are geometric
obligations; the global error bound is no longer an independent premise. -/
theorem guba23_boundary_transfer (arcs : List (RawWord × RawWord))
    (w : F) (P : ℚ) (hP : 0 ≤ P)
    (hcount : arcs.length ≤ 3)
    (hsub : (arcs.flatMap Prod.snd).Sublist (FreeGroup.invRev w.toWord))
    (hlocal : ∀ q ∈ arcs,
      (9/10 : ℚ) * (rawWeight q.1 : ℚ) - (2/10^19 : ℚ) * P ≤
        (rawWeight q.2 : ℚ)) :
    (9/10 : ℚ) * ((arcs.map (fun q => rawWeight q.1)).sum : ℚ) -
      (6/10^19 : ℚ) * P ≤ (weightedLength w : ℚ) := by
  have ht := guba23_arc_transfer_sum arcs P hlocal
  have hb := guba23_outer_arcs_weight arcs (FreeGroup.invRev w.toWord) hsub
  rw [rawWeight_invRev] at hb
  have hbQ : ((arcs.map (fun q => rawWeight q.2)).sum : ℚ) ≤
      (weightedLength w : ℚ) := by
    unfold weightedLength
    exact_mod_cast hb
  have hc : (arcs.length : ℚ) ≤ 3 := by exact_mod_cast hcount
  have he : 0 ≤ (2/10^19 : ℚ) * P := mul_nonneg (by norm_num) hP
  have herr := mul_le_mul_of_nonneg_right hc he
  linarith only [ht, hbQ, herr]

set_option maxHeartbeats 2000000 in
/-- Apply the numerical conclusion directly to literal arc readings.
Only retained coverage, local transfer, the arc count and disjointness
certificate remain as hypotheses; none is an added axiom. -/
theorem guba23_row_perimeter_of_arcs (pick : WeightedSelector)
    (n : ℕ) (i : RankHeight n) (w : F)
    (h : ∃ u : F, ¬ Good (gubaState pick i.1.val).1 u)
    (hk : i.2 ≠ 0) (arcs : List (RawWord × RawWord))
    (hcount : arcs.length ≤ 3)
    (hsub : (arcs.flatMap Prod.snd).Sublist (FreeGroup.invRev w.toWord))
    (hcover : (95/100 - 18/10^11) *
      ((2 * positiveWeight (activeLongWord pick i.1.val h) +
        i.2.natAbs * weightedLength (pick (gubaState pick i.1.val).1 h).val : ℕ) : ℚ) <
      ((arcs.map (fun q => rawWeight q.1)).sum : ℚ))
    (hlocal : ∀ q ∈ arcs,
      (9/10 : ℚ) * (rawWeight q.1 : ℚ) - (2/10^19 : ℚ) *
        (rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) : ℚ) ≤
        (rawWeight q.2 : ℚ)) :
    4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n i) <
      5 * weightedLength w := by
  apply guba23_row_perimeter_of_coverage pick n i w h hk
    ((arcs.map (fun q => rawWeight q.1)).sum : ℚ) hcover
  exact guba23_boundary_transfer arcs w _ (by positivity) hcount hsub hlocal

#print axioms guba23_sublist_weight
#print axioms guba23_flatMap_weight
#print axioms guba23_outer_arcs_weight
#print axioms guba23_arc_transfer_sum
#print axioms guba23_boundary_transfer
#print axioms guba23_row_perimeter_of_arcs



/-! ## Lemma 22: actual component partition and loss of short sections

Use the actual connectivity relation of the finite ribbon, including
after coefficient-region refinement. A component can have more than
two boundary outlets, so this partition is not yet a system of
Guba contiguity subdiagrams. The separate pruning lemma below implements
the last step of Lemma 22 once the preferred system from Lemma 19 and
the local bounds and multiplicity estimate are established.
-/

/-- Each support consists of actual darts of a specified boundary set
in the component of the chosen representative. -/
noncomputable def guba22_component_support {D : Type}
    (P : RibbonMap D) (B : Finset D) (a : D) : Finset D := by
  classical
  exact B.filter (P.SameComponent a)

theorem guba22_mem_component_support {D : Type} (P : RibbonMap D)
    (B : Finset D) (a d : D) :
    d ∈ guba22_component_support P B a ↔ d ∈ B ∧ P.SameComponent a d := by
  classical
  simp [guba22_component_support]

/-- Distinct components cannot share even a single boundary dart. -/
theorem guba22_component_support_disjoint {D : Type} (P : RibbonMap D)
    (B : Finset D) (a b : D) (h : ¬ P.SameComponent a b) :
    Disjoint (guba22_component_support P B a)
      (guba22_component_support P B b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d ha hb
  have ha' := (guba22_mem_component_support P B a d).mp ha
  have hb' := (guba22_mem_component_support P B b d).mp hb
  exact h (Relation.EqvGen.trans _ _ _ ha'.2
    (Relation.EqvGen.symm _ _ hb'.2))

/-- Choose one representative of each actual component meeting B.
This is an existence theorem, not a postulated partition. -/
theorem guba22_exists_component_representatives {D : Type}
    (P : RibbonMap D) (B : Finset D) :
    ∃ R : Finset D, R ⊆ B ∧
      (∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ P.SameComponent a b) ∧
      (∀ d ∈ B, ∃ a ∈ R, P.SameComponent a d) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    exact ⟨∅, by simp, by simp, by simp⟩
  | @insert d B _hd ih =>
    obtain ⟨R, hsub, hsep, hcov⟩ := ih
    by_cases hex : ∃ a ∈ R, P.SameComponent a d
    · refine ⟨R, ?_, hsep, ?_⟩
      · intro a ha
        exact Finset.mem_insert_of_mem (hsub ha)
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hex
        · exact hcov e he
    · refine ⟨insert d R, ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsub ha)
      · intro a ha b hb hab hconn
        rcases Finset.mem_insert.mp ha with had | haR
        · rcases Finset.mem_insert.mp hb with hbd | hbR
          · exact hab (had.trans hbd.symm)
          · subst a
            exact hex ⟨b, hbR, Relation.EqvGen.symm _ _ hconn⟩
        · rcases Finset.mem_insert.mp hb with hbd | hbR
          · exact hex ⟨a, haR, by simpa only [hbd] using hconn⟩
          · exact hsep a haR b hbR hab hconn
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨_, Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩
        · obtain ⟨a, ha, hac⟩ := hcov e he
          exact ⟨a, Finset.mem_insert_of_mem ha, hac⟩

/-- The component supports really partition B, and every dart weight
is counted exactly once. This applies to the actual refined ribbon
and to the actual letter weights, not only to a list of lengths. -/
theorem guba22_component_partition_weight {D : Type}
    (P : RibbonMap D) (B : Finset D) (weight : D → ℕ) :
    ∃ R : Finset D, R ⊆ B ∧
      Set.PairwiseDisjoint (↑R : Set D) (guba22_component_support P B) ∧
      (∑ a ∈ R, ∑ d ∈ guba22_component_support P B a, weight d) =
        ∑ d ∈ B, weight d := by
  classical
  obtain ⟨R, hsub, hsep, hcov⟩ :=
    guba22_exists_component_representatives P B
  have hdis : Set.PairwiseDisjoint (↑R : Set D)
      (guba22_component_support P B) := by
    intro a ha b hb hab
    exact guba22_component_support_disjoint P B a b (hsep a ha b hb hab)
  have hunion : R.biUnion (guba22_component_support P B) = B := by
    ext d
    constructor
    · intro hd
      obtain ⟨a, _, hda⟩ := Finset.mem_biUnion.mp hd
      exact ((guba22_mem_component_support P B a d).mp hda).1
    · intro hd
      obtain ⟨a, ha, hda⟩ := hcov d hd
      exact Finset.mem_biUnion.mpr
        ⟨a, ha, (guba22_mem_component_support P B a d).mpr ⟨hd,hda⟩⟩
  refine ⟨R, hsub, hdis, ?_⟩
  rw [← Finset.sum_biUnion hdis, hunion]

/-- The cardinality calculation in Lemma 22: at most twelve first-kind
sections, six second-kind sections and two distinct corridors per pair.
The injective coding is the geometric multiplicity obligation. -/
theorem guba22_second_kind_card {A : Type} (bad : Finset A)
    (code : A → Fin 12 × Fin 6 × Fin 2)
    (hinj : Set.InjOn code (↑bad : Set A)) :
    bad.card ≤ 144 := by
  classical
  have hc := Finset.card_le_card_of_injOn code
    (t := (Finset.univ : Finset (Fin 12 × Fin 6 × Fin 2)))
    (fun _ _ => Finset.mem_univ _) hinj
  simpa using hc

/-- Prune the second-kind corridors. k stands for the nonnegative real
coefficient omega^(3/2); the proof is uniform in k and uses no
approximation. In Guba's proof each discarded arc contributes <= 2*k*D
and the preferred system initially covers >= (eta+300*k)*D.
The statement is conditional on these geometric estimates. -/
theorem guba22_prune_coverage {A : Type} [DecidableEq A]
    (s bad : Finset A) (hbad : bad ⊆ s) (weight : A → ℝ)
    (D k : ℝ) (hD : 0 ≤ D) (hk : 0 ≤ k)
    (hcard : bad.card ≤ 144)
    (hlocal : ∀ a ∈ bad, weight a ≤ 2 * k * D)
    (hcover : (95/100 + 300*k) * D ≤ ∑ a ∈ s, weight a) :
    (95/100 : ℝ) * D ≤ ∑ a ∈ s \ bad, weight a := by
  have hloss : (∑ a ∈ bad, weight a) ≤ (bad.card : ℝ) * (2*k*D) := by
    calc
      (∑ a ∈ bad, weight a) ≤ ∑ _a ∈ bad, (2*k*D) :=
        Finset.sum_le_sum hlocal
      _ = _ := by simp [nsmul_eq_mul]
  have hc : (bad.card : ℝ) ≤ 144 := by exact_mod_cast hcard
  have hkd : 0 ≤ 2*k*D := mul_nonneg (mul_nonneg (by norm_num) hk) hD
  have hloss' := hloss.trans (mul_le_mul_of_nonneg_right hc hkd)
  have hsplit := Finset.sum_sdiff (f := weight) hbad
  have hn : 0 ≤ k*D := mul_nonneg hk hD
  nlinarith only [hcover, hloss', hsplit, hn]

/-- Actual set-theoretic pruning preserves the no-common-cell and
no-common-boundary-dart conditions, as well as the no-merge condition.
The supports and merge predicate must be supplied by the geometric
construction; no claim of their existence is hidden in this result. -/
theorem guba22_prune_preserves_geometry {A C D : Type} [DecidableEq A]
    (s bad : Finset A) (cells : A → Finset C) (edges : A → Finset D)
    (merge : A → A → Prop)
    (hc : Set.PairwiseDisjoint (↑s : Set A) cells)
    (he : Set.PairwiseDisjoint (↑s : Set A) edges)
    (hm : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ merge a b) :
    Set.PairwiseDisjoint (↑(s \ bad) : Set A) cells ∧
      Set.PairwiseDisjoint (↑(s \ bad) : Set A) edges ∧
      (∀ a ∈ s \ bad, ∀ b ∈ s \ bad, a ≠ b → ¬ merge a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hc (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab
  · intro a ha b hb hab
    exact he (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab
  · intro a ha b hb hab
    exact hm a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1 hab

#print axioms guba22_component_support
#print axioms guba22_mem_component_support
#print axioms guba22_component_support_disjoint
#print axioms guba22_exists_component_representatives
#print axioms guba22_component_partition_weight
#print axioms guba22_second_kind_card
#print axioms guba22_prune_coverage
#print axioms guba22_prune_preserves_geometry



/-! ## Two-outlet regions in the actual coefficient ribbon

The two-outlet condition is a property of a genuine component of the
refined permutation map. It is not a choice of arbitrary paired
words. Here we prove mutual normal-closure dependence of the two
outlet readings by the spherical boundary theorem. This is weaker
than conjugacy or the full quadrilateral/contiguity construction.
-/

/-- The preserved vertex readings of the coefficient region have
not changed, even though all the non-coefficient vertices were split. -/
theorem guba22_coefficient_preserved_read {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter)
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (d : D) (hd : keep d) :
    ((P.coefficientRegions keep hkeep).vertexBoundary d).map read =
      (P.vertexBoundary d).map read := by
  classical
  let S := P.coefficientRegions keep hkeep
  change (S.vertexBoundary d).map read = _
  have hag : ∀ e, P.rotation.SameCycle d e → S.rotation e = P.rotation e := by
    intro e hde
    have hk : keep e := by
      obtain ⟨m, hm⟩ := hde.exists_nat_pow_eq
      rw [← hm]
      clear hm hde
      induction m with
      | zero => exact hd
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (hkeep _).mpr ih
    simp [S, RibbonMap.coefficientRegions_rotation, hk]
  change (((P.withRotation S.rotation).vertexBoundary d).map read) = _
  exact congrArg (List.map read) (refined_vertex_read_of_agreement P S.rotation d hag)

/-- If all the coefficient vertices are trivial in a normal quotient
and the component has only the two indicated outlets, killing the
second outlet forces the first to vanish in the same quotient. -/
theorem guba22_two_outlet_mem_of_other {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a b : D) (ha : ¬keep a) (hb : ¬keep b)
    (honly : ∀ d, (P.coefficientRegions keep hkeep).SameComponent a d →
      ¬keep d → d = a ∨ d = b)
    (hmb : FreeGroup.mk [read b] ∈ N) :
    FreeGroup.mk [read a] ∈ N := by
  classical
  let S := P.coefficientRegions keep hkeep
  have hSa : S.rotation a = a := by
    simp [S, RibbonMap.coefficientRegions_rotation, ha]
  have hSb : S.rotation b = b := by
    simp [S, RibbonMap.coefficientRegions_rotation, hb]
  have hm := component_boundary_mem_normal S read N (fun d => he d)
    (P.coefficientRegions_euler keep hkeep hE) a (by
      intro d hc hnc
      by_cases hd : keep d
      · change FreeGroup.mk
          (((P.coefficientRegions keep hkeep).vertexBoundary d).map read) ∈ N
        rw [guba22_coefficient_preserved_read P read keep hkeep d hd]
        exact hint d hd
      · rcases honly d hc hd with hda | hdb
        · exact (hnc (by rw [hda])).elim
        · rw [hdb, fixed_vertex_read_singleton S b hSb]
          simpa only [List.map_cons, List.map_nil] using hmb)
  rw [fixed_vertex_read_singleton S a hSa] at hm
  simpa only [List.map_cons, List.map_nil] using hm

/-- The preceding implication is symmetric for two outlets in one
actual connected component. In particular nonvanishing propagates
from either outlet to the other. -/
theorem guba22_two_outlet_mem_iff {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a b : D) (ha : ¬keep a) (hb : ¬keep b)
    (hab : (P.coefficientRegions keep hkeep).SameComponent a b)
    (honly : ∀ d, (P.coefficientRegions keep hkeep).SameComponent a d →
      ¬keep d → d = a ∨ d = b) :
    FreeGroup.mk [read a] ∈ N ↔ FreeGroup.mk [read b] ∈ N := by
  constructor
  · apply guba22_two_outlet_mem_of_other P read N keep hkeep hE he hint b a hb ha
    intro d hbd hd
    exact (honly d (Relation.EqvGen.trans _ _ _ hab hbd) hd).symm
  · exact guba22_two_outlet_mem_of_other P read N keep hkeep hE he hint a b ha hb honly

/-- A two-element component support is an actual pair, not merely
an upper bound on the number of outlets. -/
theorem guba22_component_support_pair {D : Type} [DecidableEq D]
    (P : RibbonMap D) (B : Finset D) (a b : D)
    (ha : a ∈ B) (hb : b ∈ B) (hab : P.SameComponent a b)
    (honly : ∀ d ∈ B, P.SameComponent a d → d = a ∨ d = b) :
    guba22_component_support P B a = {a,b} := by
  ext d
  rw [guba22_mem_component_support]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hconn⟩
    exact honly d hd hconn
  · rintro (rfl | rfl)
    · exact ⟨ha, Relation.EqvGen.refl _⟩
    · exact ⟨hb, hab⟩

/-- A nonvanishing outlet cannot occur in a singleton component.
Consequently, if its actual outlet support has cardinality at most
two, it has exactly one other outlet. -/
theorem guba22_exists_unique_other_outlet {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a : D) (ha : ¬keep a) (hna : FreeGroup.mk [read a] ∉ N)
    (hcap : ∀ b c, (P.coefficientRegions keep hkeep).SameComponent a b →
      (P.coefficientRegions keep hkeep).SameComponent a c →
      ¬keep b → ¬keep c → b ≠ a → c ≠ a → b = c) :
    ∃! b, (P.coefficientRegions keep hkeep).SameComponent a b ∧
      ¬keep b ∧ b ≠ a := by
  obtain ⟨b, hab, hb, hba⟩ :=
    coefficientRegions_no_unique_outlet P read N keep hkeep hE he hint a ha hna
  refine ⟨b, ⟨hab,hb,hba⟩, ?_⟩
  intro c hc
  exact hcap c b hc.1 hab hc.2.1 hb hc.2.2 hba

#print axioms guba22_coefficient_preserved_read
#print axioms guba22_two_outlet_mem_of_other
#print axioms guba22_two_outlet_mem_iff
#print axioms guba22_component_support_pair
#print axioms guba22_exists_unique_other_outlet



/-! ## Nonabelian two-boundary theorem by actual planar splicing

The splicing operation retains every dart, merges two distinct vertices,
and decreases the number of vertices by one. Thus we can use induction
on vertex count, without choosing a hypothetical system of corridors.
-/

open SmallPresentationStatements.PermutationCycles

/-- The complete based products at two corners of the same vertex
are conjugate, with an explicit group element as witness. -/
theorem guba22_cycleProduct_conjugator {D K : Type} [Finite D] [Group K]
    (sigma : Equiv.Perm D) (v : D → K) (a b : D)
    (hab : sigma.SameCycle a b) :
    ∃ g : K, cycleProduct sigma v b =
      g * cycleProduct sigma v a * g⁻¹ := by
  obtain ⟨m, hm⟩ := hab.exists_nat_pow_eq
  rw [← hm]
  clear hm hab
  induction m with
  | zero =>
    exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    let d := (sigma ^ m) a
    obtain ⟨l, hl⟩ := cycleBoundary_cons sigma d
    have hnext : cycleProduct sigma v (sigma d) =
        (v d)⁻¹ * cycleProduct sigma v d * v d := by
      simp only [cycleProduct, cycleBoundary_next sigma d l hl, hl,
        List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      group
    rw [pow_succ', Equiv.Perm.mul_apply]
    change ∃ k : K, cycleProduct sigma v (sigma d) =
      k * cycleProduct sigma v a * k⁻¹
    refine ⟨(v d)⁻¹ * g, ?_⟩
    rw [hnext, show cycleProduct sigma v d =
      g * cycleProduct sigma v a * g⁻¹ from hg]
    group

/-- There is an actual edge leaving the vertex of a whenever a
connected ribbon has a second vertex. -/
theorem guba22_exists_leaving_edge {D : Type} (P : RibbonMap D)
    (hc : P.Connected) (a b : D) (hab : ¬ P.rotation.SameCycle a b) :
    ∃ c, P.rotation.SameCycle a c ∧ ¬ P.rotation.SameCycle a (P.edge c) := by
  classical
  by_contra hx
  have hclosed : ∀ e, P.rotation.SameCycle a e →
      P.rotation.SameCycle a (P.edge e) := by
    intro e he
    by_contra hn
    exact hx ⟨e,he,hn⟩
  have hedge (d : D) : P.rotation.SameCycle a (P.edge d) ↔
      P.rotation.SameCycle a d := by
    constructor
    · intro h
      simpa only [P.edge_involutive d] using hclosed (P.edge d) h
    · exact hclosed d
  exact hab ((P.invariant_on_component (P.rotation.SameCycle a) hedge
    (fun d => Equiv.Perm.sameCycle_apply_right) (hc a b)).mp (.refl _ _))

/-- Splicing an edge between distinct vertices preserves connectedness. -/
theorem guba22_edgeSplice_connected {D : Type} [Fintype D]
    (P : RibbonMap D) (hc : P.Connected) (c : D)
    (hn : ¬ P.rotation.SameCycle c (P.edge c)) :
    (P.edgeSplice c).Connected := by
  classical
  have hcard := P.card_components_of_connected hc c
  have hs := (P.edgeSplice_counts c hn).2.2.2
  have hsub : Subsingleton (P.edgeSplice c).Component :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  intro d e
  exact Quotient.exact (hsub.elim ((P.edgeSplice c).componentClass d)
    ((P.edgeSplice c).componentClass e))

/-- Two distinct exceptional vertices in a connected spherical ribbon
have inverse-conjugate based products. All other vertices have product
one. No bound on the conjugator is claimed here. -/
theorem guba22_two_boundary_product {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hc : P.Connected) (hE : P.EulerEquality)
    (a b : D) (hab : ¬ P.rotation.SameCycle a b)
    (hint : ∀ d, ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d → cycleProduct P.rotation v d = 1) :
    ∃ g : K, cycleProduct P.rotation v a * g *
      cycleProduct P.rotation v b * g⁻¹ = 1 := by
  classical
  obtain ⟨c, hac, hce⟩ := guba22_exists_leaving_edge P hc a b hab
  have hn : ¬ P.rotation.SameCycle c (P.edge c) :=
    fun h => hce (hac.trans h)
  have hnc : ¬ P.rotation.SameCycle (P.rotation c) (P.edge c) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  let S := P.edgeSplice c
  have hES : S.EulerEquality := (P.edgeSplice_euler_iff c hn).mpr hE
  have hCS : S.Connected := guba22_edgeSplice_connected P hc c hn
  have hca : P.rotation.SameCycle a (P.rotation c) :=
    hac.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  obtain ⟨p, hp⟩ := guba22_cycleProduct_conjugator P.rotation v a
    (P.rotation c) hca
  have hmerge : cycleProduct S.rotation v (P.rotation c) =
      cycleProduct P.rotation v (P.rotation c) *
        cycleProduct P.rotation v (P.edge c) :=
    cycleProduct_cutAt_merge P.rotation v (P.rotation c) (P.edge c) hnc
  have unchanged (d : D) (hd : ¬ S.rotation.SameCycle (P.rotation c) d) :
      cycleProduct S.rotation v d = cycleProduct P.rotation v d := by
    have ha' : ¬ P.rotation.SameCycle d (P.rotation c) := by
      intro hh
      exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc hh.symm)
    have hb' : ¬ P.rotation.SameCycle d (P.edge c) := by
      intro hh
      have h0 : S.rotation.SameCycle (P.rotation c) (P.edge c) :=
        cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc
      exact hd (h0.trans (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc hh.symm))
    exact cycleProduct_cutAt_unchanged P.rotation v _ _ _ ha' hb'
  have hnA (d : D) (hd : ¬ S.rotation.SameCycle (P.rotation c) d) :
      ¬ P.rotation.SameCycle a d := by
    intro h
    exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc (hca.symm.trans h))
  by_cases hb : P.rotation.SameCycle b (P.edge c)
  · obtain ⟨q, hq⟩ := guba22_cycleProduct_conjugator P.rotation v b (P.edge c) hb
    have hprod : cycleProduct S.rotation v (P.rotation c) = 1 := by
      apply RibbonMap.boundary_product_one D S v (fun d => he d) hCS hES
      intro d hd
      have hnB : ¬ P.rotation.SameCycle b d := by
        intro h
        have h0 : S.rotation.SameCycle (P.rotation c) (P.edge c) :=
          cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc
        exact hd (h0.trans
          (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc (hb.symm.trans h)))
      change cycleProduct S.rotation v d = 1
      rw [unchanged d hd]
      exact hint d (hnA d hd) hnB
    have hh : cycleProduct P.rotation v (P.rotation c) *
        cycleProduct P.rotation v (P.edge c) = 1 := hmerge.symm.trans hprod
    refine ⟨p⁻¹ * q, ?_⟩
    calc
      _ = p⁻¹ * (cycleProduct P.rotation v (P.rotation c) *
          cycleProduct P.rotation v (P.edge c)) * p := by rw [hp,hq]; group
      _ = 1 := by rw [hh]; simp
  · have hB : ¬ S.rotation.SameCycle (P.rotation c) b := by
      intro hh
      rcases (P.edgeSplice_sameVertex_iff c hn _ _).mp hh with h | h
      · exact hab (hca.trans h)
      · rcases h.2 with h' | h'
        · exact hab (hac.trans h'.symm)
        · exact hb h'
    have hother : cycleProduct P.rotation v (P.edge c) = 1 :=
      hint _ hce hb
    have hprodA : cycleProduct S.rotation v (P.rotation c) =
        p * cycleProduct P.rotation v a * p⁻¹ := by
      rw [hmerge, hother, mul_one, hp]
    have hprodB := unchanged b hB
    obtain ⟨g, hg⟩ := guba22_two_boundary_product S v (fun d => he d) hCS hES
      (P.rotation c) b hB (by
        intro d hd hbd
        rw [unchanged d hd]
        apply hint d (hnA d hd)
        intro hh
        exact hbd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc hh))
    refine ⟨p⁻¹ * g, ?_⟩
    calc
      _ = p⁻¹ * (cycleProduct S.rotation v (P.rotation c) * g *
          cycleProduct S.rotation v b * g⁻¹) * p := by
            rw [hprodA,hprodB]; group
      _ = 1 := by rw [hg]; simp
termination_by Fintype.card P.Vertex
decreasing_by
  have hcount := (P.edgeSplice_counts c hn).1
  change Fintype.card (P.edgeSplice c).Vertex < Fintype.card P.Vertex
  omega

#print axioms guba22_cycleProduct_conjugator
#print axioms guba22_exists_leaving_edge
#print axioms guba22_edgeSplice_connected
#print axioms guba22_two_boundary_product



/-- Apply the two-boundary theorem to the actual connected coefficient
region, in the normal quotient containing all its retained rows.
The boundary outlets are singleton vertices, so the resulting
conjugacy relates their exact letter values. -/
theorem guba22_two_outlet_inverse_conjugacy {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a b : D) (ha : ¬keep a) (hb : ¬keep b) (hne : a ≠ b)
    (hab : (P.coefficientRegions keep hkeep).SameComponent a b)
    (honly : ∀ d, (P.coefficientRegions keep hkeep).SameComponent a d →
      ¬keep d → d = a ∨ d = b) :
    ∃ g : F ⧸ N,
      QuotientGroup.mk' N (FreeGroup.mk [read a]) * g *
        QuotientGroup.mk' N (FreeGroup.mk [read b]) * g⁻¹ = 1 := by
  classical
  let S := P.coefficientRegions keep hkeep
  let C := S.componentRibbon a
  let q := QuotientGroup.mk' N
  let x : {d : D // S.SameComponent a d} := ⟨a, Relation.EqvGen.refl a⟩
  let y : {d : D // S.SameComponent a d} := ⟨b, hab⟩
  let v : {d : D // S.SameComponent a d} → F ⧸ N :=
    fun d => q (FreeGroup.mk [read d.val])
  have hES : S.EulerEquality := P.coefficientRegions_euler keep hkeep hE
  have hEC : C.EulerEquality := by
    change Fintype.card (S.componentRibbon a).Vertex +
      Fintype.card (S.componentRibbon a).Face =
      Fintype.card (S.componentRibbon a).Edge +
        2 * Fintype.card (S.componentRibbon a).Component
    rw [S.componentRibbon_card_components, mul_one]
    exact S.componentRibbon_sphere hES a
  have hSa : S.rotation a = a := by
    simp [S, RibbonMap.coefficientRegions_rotation, ha]
  have hSb : S.rotation b = b := by
    simp [S, RibbonMap.coefficientRegions_rotation, hb]
  have hfix {d e : D} (hd : S.rotation d = d)
      (hc : S.rotation.SameCycle d e) : d = e := by
    obtain ⟨m, hm⟩ := hc.exists_nat_pow_eq
    rw [← hm]
    clear hm hc
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← ih, hd]
  have hxy : ¬ C.rotation.SameCycle x y := by
    intro h
    have hh := (S.restrict_sameVertex_iff (S.SameComponent a)
      (S.component_membership_edge a) (S.component_membership_rotation a) x y).mp h
    exact hne (hfix hSa hh)
  have eval (ds : List {d : D // S.SameComponent a d}) :
      (ds.map v).prod = q (FreeGroup.mk (ds.map (fun d => read d.val))) := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons d ds ih =>
      change v d * (ds.map v).prod =
        q (FreeGroup.mk ([read d.val] ++ ds.map (fun e => read e.val)))
      rw [ih, ← FreeGroup.mul_mk, map_mul]
  have hread (d : {d : D // S.SameComponent a d}) :
      cycleProduct C.rotation v d =
        q (FreeGroup.mk ((S.vertexBoundary d.val).map read)) := by
    change ((C.vertexBoundary d).map v).prod = _
    rw [eval, component_vertex_read S read a d]
  obtain ⟨g, hg⟩ := guba22_two_boundary_product C v
    (by
      intro d
      change q (FreeGroup.mk [read (S.edge d.val)]) =
        (q (FreeGroup.mk [read d.val]))⁻¹
      rw [show S.edge d.val = P.edge d.val from rfl, he,
        signedLetterValue_reverse, map_inv])
    (S.componentRibbon_connected a) hEC x y hxy (by
      intro d hdx hdy
      have hd : keep d.val := by
        by_contra hn
        rcases honly d.val d.property hn with h | h
        · have hh : x = d := Subtype.ext h.symm
          apply hdx
          rw [← hh]
        · have hh : y = d := Subtype.ext h.symm
          apply hdy
          rw [← hh]
      rw [hread]
      change q (FreeGroup.mk
        (((P.coefficientRegions keep hkeep).vertexBoundary d.val).map read)) = 1
      rw [guba22_coefficient_preserved_read P read keep hkeep d.val hd]
      exact (QuotientGroup.eq_one_iff _).mpr (hint d.val hd))
  refine ⟨g, ?_⟩
  rw [hread x, hread y] at hg
  change q (FreeGroup.mk ((S.vertexBoundary a).map read)) * g *
    q (FreeGroup.mk ((S.vertexBoundary b).map read)) * g⁻¹ = 1 at hg
  rw [fixed_vertex_read_singleton S a hSa, fixed_vertex_read_singleton S b hSb] at hg
  simpa only [List.map_cons, List.map_nil] using hg

#print axioms guba22_two_outlet_inverse_conjugacy



/-! ## Literal intervals on distinct peripheral vertices

A single dart is not a contiguity section. We now isolate prescribed
nonempty proper intervals on two different original vertices, in one
actual split refinement. The lengths, order, and original incidences
are retained. An edge between the intervals guarantees that their
new vertices lie in the same genuine component.
-/

/-- A cut in a different vertex does not change any iterate along
the original cycle of the protected starting dart. -/
theorem guba22_other_cycle_iterate {D : Type} [Fintype D]
    (P : RibbonMap D) (a b c : D)
    (ha : ¬ P.rotation.SameCycle c a)
    (hb : ¬ P.rotation.SameCycle c b) (m : ℕ) :
    (P.vertexCut a b).rotation^[m] c = P.rotation^[m] c := by
  classical
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have hcycle : P.rotation.SameCycle c (P.rotation^[m] c) := by
      rw [← Equiv.Perm.coe_pow]
      exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    rw [P.vertexCut_rotation, cutAt_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      apply ha
      rw [← h]
      exact Equiv.Perm.sameCycle_apply_right.mpr hcycle
    · intro h
      apply hb
      rw [← h]
      exact Equiv.Perm.sameCycle_apply_right.mpr hcycle

/-- Actual finite cuts isolate two prescribed proper boundary
intervals simultaneously, with both literal ordered dart lists.
No assumption about the metric or the relator labels is needed. -/
theorem guba22_two_interval_refinement {D : Type} [Fintype D]
    (P : RibbonMap D) (a c : D) (k l : ℕ)
    (hk : k + 1 < Function.minimalPeriod P.rotation a)
    (hl : l + 1 < Function.minimalPeriod P.rotation c)
    (hac : ¬ P.rotation.SameCycle a c) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (P.withRotation tau).vertexBoundary a =
        List.ofFn (fun i : Fin k => P.rotation^[i.val] a) ++ [P.rotation^[k] a] ∧
      (P.withRotation tau).vertexBoundary c =
        List.ofFn (fun i : Fin l => P.rotation^[i.val] c) ++ [P.rotation^[l] c] ∧
      ¬ tau.SameCycle a c := by
  classical
  let b := P.rotation^[k+1] a
  let d := P.rotation^[l+1] c
  let S := P.vertexCut a b
  have h1 : P.rotation.SameCycle a b := by
    change P.rotation.SameCycle a (P.rotation^[k+1] a)
    rw [← Equiv.Perm.coe_pow]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  have h2 : P.rotation.SameCycle c d := by
    change P.rotation.SameCycle c (P.rotation^[l+1] c)
    rw [← Equiv.Perm.coe_pow]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  have hab : a ≠ b := by
    intro h
    have he : P.rotation^[0] a = P.rotation^[k+1] a := h
    have hzero : (0 : ℕ) = k+1 := Function.iterate_injOn_Iio_minimalPeriod
      (f := (P.rotation : D → D)) (x := a)
      (show 0 ∈ Set.Iio (Function.minimalPeriod P.rotation a) from by
        change 0 < Function.minimalPeriod P.rotation a
        omega) hk he
    omega
  have hcd : c ≠ d := by
    intro h
    have he : P.rotation^[0] c = P.rotation^[l+1] c := h
    have hzero : (0 : ℕ) = l+1 := Function.iterate_injOn_Iio_minimalPeriod
      (f := (P.rotation : D → D)) (x := c)
      (show 0 ∈ Set.Iio (Function.minimalPeriod P.rotation c) from by
        change 0 < Function.minimalPeriod P.rotation c
        omega) hl he
    omega
  have hca : ¬ P.rotation.SameCycle c a := fun h => hac h.symm
  have hcb : ¬ P.rotation.SameCycle c b := fun h => hac (h1.trans h.symm)
  have hcread : S.vertexBoundary c = P.vertexBoundary c :=
    vertexCut_other_vertex_read P a b c hca hcb
  have hperiod : Function.minimalPeriod S.rotation c =
      Function.minimalPeriod P.rotation c := by
    have hlen := congrArg List.length hcread
    simpa only [RibbonMap.vertexBoundary, List.length_ofFn] using hlen
  have hiter (m : ℕ) : S.rotation^[m] c = P.rotation^[m] c :=
    guba22_other_cycle_iterate P a b c hca hcb m
  have hd : S.rotation^[l+1] c = d := hiter _
  have h2' : S.rotation.SameCycle c d := by
    apply (S.mem_vertexBoundary_iff c d).mp
    rw [hcread]
    exact (P.mem_vertexBoundary_iff c d).mpr h2
  have hca' : ¬ S.rotation.SameCycle c a := by
    intro h
    have hm := (S.mem_vertexBoundary_iff c a).mpr h
    rw [hcread] at hm
    exact hca ((P.mem_vertexBoundary_iff c a).mp hm)
  let T := S.vertexCut c d
  have haRead : T.vertexBoundary a = S.vertexBoundary a :=
    vertexCut_other_vertex_read S c d a
      (fun h => hca' h.symm) (fun h => hca' (h2'.trans h.symm))
  have hcRead := vertexCut_prescribed_interval S c l (by rw [hperiod]; exact hl)
  rw [hd] at hcRead
  refine ⟨T.rotation, SplitRefinement.cut
    (SplitRefinement.single P.rotation a b hab h1) c d hcd h2', ?_, ?_, ?_⟩
  · change T.vertexBoundary a = _
    rw [haRead]
    exact vertexCut_prescribed_interval P a k hk
  · change T.vertexBoundary c = _
    rw [hcRead, hiter l]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact hiter i.val
  · intro h
    have hm := (T.mem_vertexBoundary_iff a c).mpr h
    rw [haRead] at hm
    exact hca' ((S.mem_vertexBoundary_iff a c).mp hm).symm

/-- If one actual edge meets both prescribed intervals, their
isolated vertices belong to the same component after the two cuts.
This supplies a concrete two-interval region candidate, not a
claim that it has no further peripheral vertices. -/
theorem guba22_connected_interval_refinement {D : Type} [Fintype D]
    (P : RibbonMap D) (a c e : D) (k l : ℕ)
    (hk : k + 1 < Function.minimalPeriod P.rotation a)
    (hl : l + 1 < Function.minimalPeriod P.rotation c)
    (hac : ¬ P.rotation.SameCycle a c)
    (he : e ∈ List.ofFn (fun i : Fin k => P.rotation^[i.val] a) ++
      [P.rotation^[k] a])
    (he' : P.edge e ∈ List.ofFn (fun i : Fin l => P.rotation^[i.val] c) ++
      [P.rotation^[l] c]) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (P.withRotation tau).vertexBoundary a =
        List.ofFn (fun i : Fin k => P.rotation^[i.val] a) ++ [P.rotation^[k] a] ∧
      (P.withRotation tau).vertexBoundary c =
        List.ofFn (fun i : Fin l => P.rotation^[i.val] c) ++ [P.rotation^[l] c] ∧
      ¬ tau.SameCycle a c ∧ (P.withRotation tau).SameComponent a c := by
  obtain ⟨tau, href, ha, hc, hne⟩ :=
    guba22_two_interval_refinement P a c k l hk hl hac
  let S := P.withRotation tau
  have h1 : S.rotation.SameCycle a e :=
    (S.mem_vertexBoundary_iff a e).mp (by rw [show S.vertexBoundary a = _ from ha]; exact he)
  have h2 : S.rotation.SameCycle c (S.edge e) :=
    (S.mem_vertexBoundary_iff c (S.edge e)).mp (by
      rw [show S.vertexBoundary c = _ from hc]
      exact he')
  refine ⟨tau,href,ha,hc,hne,?_⟩
  exact Relation.EqvGen.trans _ _ _ (S.component_of_vertexCycle h1)
    (Relation.EqvGen.trans _ _ _ (S.component_edge e)
      (S.component_of_vertexCycle h2.symm))

#print axioms guba22_other_cycle_iterate
#print axioms guba22_two_interval_refinement
#print axioms guba22_connected_interval_refinement



/-! ## Spherical incidence bounds for a compressed contiguity graph

The dart type and its vertex/edge/face quotients are the actual ones
of a ribbon. The face-degree condition is derived from excluding
one- and two-corner face walks, not imposed as an unrelated graph
count. To use this on Guba's preferred system we still need to
construct the compressed ribbon and account for its exceptional faces.
-/

/-- The absence of one- and two-step returns implies the lower
bound three on the actual face traversal. -/
theorem guba22_face_length_ge_three {D : Type} [Fintype D]
    (P : RibbonMap D) (d : D)
    (h1 : P.face d ≠ d) (h2 : P.face (P.face d) ≠ d) :
    3 ≤ (P.faceBoundary d).length := by
  have hp : 0 < Function.minimalPeriod P.face d :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (P.face.injective.mem_periodicPts d)
  have hret := Function.iterate_minimalPeriod (f := (P.face : D → D)) (x := d)
  have hn1 : Function.minimalPeriod P.face d ≠ 1 := by
    intro h
    rw [h, Function.iterate_one] at hret
    exact h1 hret
  have hn2 : Function.minimalPeriod P.face d ≠ 2 := by
    intro h
    rw [h] at hret
    have he : P.face (P.face d) = d := by
      simpa only [Function.iterate_succ_apply', Function.iterate_one, Function.iterate_zero, id_eq] using hret
    exact h2 he
  simp only [RibbonMap.faceBoundary, List.length_ofFn]
  omega

/-- In a loop-free ribbon, a one-corner face is impossible.
A fixed face would force the paired dart to be on the same vertex. -/
theorem guba22_no_monogon_of_no_loop {D : Type}
    (P : RibbonMap D)
    (hloop : ∀ d, ¬ P.rotation.SameCycle d (P.edge d))
    (d : D) : P.face d ≠ d := by
  intro hf
  have hh := congrArg P.rotation hf
  have he : P.edge d = P.rotation d := by
    simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using hh
  apply hloop d
  rw [he]
  exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- Euler bounds the actual number of edges in a connected spherical
ribbon with no monogon or bigon faces. This is the basic planar
counting estimate needed after suppression of inessential corridors. -/
theorem guba22_reduced_ribbon_edge_bound {D : Type} [Fintype D]
    (P : RibbonMap D) (a : D) (hc : P.Connected)
    (hE : P.EulerEquality)
    (h1 : ∀ d, P.face d ≠ d)
    (h2 : ∀ d, P.face (P.face d) ≠ d) :
    Fintype.card P.Edge + 6 ≤ 3 * Fintype.card P.Vertex := by
  have hf : 3 * Fintype.card P.Face ≤ Fintype.card D := by
    apply incidence_lower_bound P.faceOf 3
    intro f
    induction f using Quotient.inductionOn with
    | h d =>
      change 3 ≤ incidenceDegree P.faceOf (P.faceOf d)
      rw [P.face_incidenceDegree]
      exact guba22_face_length_ge_three P d (h1 d) (h2 d)
  have hd := P.card_darts
  have hcc := P.card_components_of_connected hc a
  change Fintype.card P.Vertex + Fintype.card P.Face =
    Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
  omega

/-- An exempt face can have degree below three. The precise bound
retains its actual length, rather than discarding it entirely. -/
theorem guba22_reduced_ribbon_edge_bound_except_face {D : Type} [Fintype D]
    (P : RibbonMap D) (a z : D) (hc : P.Connected)
    (hE : P.EulerEquality)
    (h1 : ∀ d, ¬ P.face.SameCycle z d → P.face d ≠ d)
    (h2 : ∀ d, ¬ P.face.SameCycle z d → P.face (P.face d) ≠ d) :
    Fintype.card P.Edge + 3 + (P.faceBoundary z).length ≤
      3 * Fintype.card P.Vertex := by
  have hf : 3 * Fintype.card P.Face + (P.faceBoundary z).length ≤
      Fintype.card D + 3 := by
    apply incidence_lower_bound_with_exception P.faceOf (P.faceOf z) 3
      (P.faceBoundary z).length
    · intro f hne
      induction f using Quotient.inductionOn with
      | h d =>
        change P.faceOf d ≠ P.faceOf z at hne
        have hn : ¬ P.face.SameCycle z d := by
          intro h
          exact hne (Quotient.sound h.symm)
        change 3 ≤ incidenceDegree P.faceOf (P.faceOf d)
        rw [P.face_incidenceDegree]
        exact guba22_face_length_ge_three P d (h1 d hn) (h2 d hn)
    · rw [P.face_incidenceDegree]
  have hd := P.card_darts
  have hcc := P.card_components_of_connected hc a
  change Fintype.card P.Vertex + Fintype.card P.Face =
    Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
  omega

#print axioms guba22_face_length_ge_three
#print axioms guba22_no_monogon_of_no_loop
#print axioms guba22_reduced_ribbon_edge_bound
#print axioms guba22_reduced_ribbon_edge_bound_except_face

/-! ## A new relation has a high-rank cell in the marked component

Disconnected closed components of a spherical realization are irrelevant
for deciding whether the boundary word is already trivial at a lower
rank. Apply the actual component boundary theorem before choosing a
cell to excise. This does not assume a perimeter estimate or a
contiguity system.
-/

/-- If the marked boundary is not killed by the earlier presentation,
its own connected component contains an interior vertex of at least
the indicated rank. In particular, for a word newly killed at rank
(n-1), that vertex has rank exactly (n-1). -/
theorem rankRibbon_boundary_component_has_high_cell (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (hw : w ≠ 1) (hnew : w ∉ weightedHeightStage pick X j) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    ∃ (d : DiscDarts (markedRows rows w) (boundaryIdentity s)) (i : RankHeight n),
      P.SameComponent z d ∧ ¬ P.rotation.SameCycle z d ∧
      (boundaryIdentity s)[discOccurrence (markedRows rows w)
        (boundaryIdentity s) d].1.2 = some i ∧ j ≤ i.1.val := by
  classical
  intro rows P z
  let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  have hinterior (k : Fin (boundaryIdentity s).length)
      (hk : k ≠ boundaryOccurrence s) :
      ∃ i : RankHeight n, (boundaryIdentity s)[k].1.2 = some i := by
    obtain ⟨v,hv⟩ := k
    cases v with
    | zero => exact (hk (Fin.ext rfl)).elim
    | succ m =>
      have hm : m < s.length := by
        simpa [boundaryIdentity] using hv
      refine ⟨s[m].1.2, ?_⟩
      simp [boundaryIdentity, markOccurrence]
  by_contra h
  have hb := component_boundary_mem_normal P read N
    (relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
      (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs))
    (boundaryRibbon_euler rows w s hs) z (by
      intro d hc hd
      have hk : discOccurrence (markedRows rows w) (boundaryIdentity s) d ≠
          boundaryOccurrence s := by
        intro he
        exact hd ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr he)
      obtain ⟨i,hi⟩ := hinterior _ hk
      have hlt : i.1.val < j := by
        by_contra! hge
        exact h ⟨d,i,hc,hd,hi,hge⟩
      exact rankRibbon_lower_vertex_mem pick X n j w s hs d i hi hlt)
  change FreeGroup.mk (((boundaryRibbon rows w s hs).vertexBoundary
    (boundaryDart rows w s hw)).map
    (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) ∈ N at hb
  rw [boundaryRibbon_read rows w s hs hw, ← FreeGroup.inv_mk, FreeGroup.mk_toWord] at hb
  exact hnew (by simpa only [inv_inv] using N.inv_mem hb)

#print axioms rankRibbon_boundary_component_has_high_cell


/-- Select the high-rank cell at its original zero corner inside the
actual connected marked component. Its literal signed row is retained
after restriction. Thus the second marked vertex has the large
perimeter of a genuine Guba row, not just a conjugate group value.
The two marked vertices do not yet supply a system of contiguity arcs. -/
theorem guba_boundary_component_large_row (pick : WeightedSelector)
    (n j : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick (gubaConjugatorChoice pick) n i)) s = w)
    (hw : w ≠ 1) (hnew : w ∉ weightedHeightStage pick (gubaConjugatorChoice pick) j) :
    let rows := rankHeightRows pick (gubaConjugatorChoice pick) n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let C := P.componentRibbon z
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∃ (d : {e : DiscDarts (markedRows rows w) (boundaryIdentity s) // P.SameComponent z e})
      (i : RankHeight n),
      ¬ C.rotation.SameCycle ⟨z, Relation.EqvGen.refl z⟩ d ∧
      (boundaryIdentity s)[discOccurrence (markedRows rows w)
        (boundaryIdentity s) d.val].1.2 = some i ∧
      j ≤ i.1.val ∧
      5 * (2 + 2 * 10^80) < 4 * rawWeight ((C.vertexBoundary d).map (fun e => read e.val)) := by
  classical
  intro rows P z C read
  obtain ⟨d,i,hc,hd,hi,hj⟩ := rankRibbon_boundary_component_has_high_cell
    pick (gubaConjugatorChoice pick) n j w s hs hw hnew
  obtain ⟨idx,k,rfl⟩ := exists_discAt (markedRows rows w) (boundaryIdentity s) d
  have hi' : (boundaryIdentity s)[idx].1.2 = some i := by
    change (boundaryIdentity s)[discOccurrence (markedRows rows w)
      (boundaryIdentity s) (discAt (markedRows rows w) (boundaryIdentity s) idx k)].1.2 = some i at hi
    have hidx := discOccurrence_at (markedRows rows w) (boundaryIdentity s) idx k
    have hlabel := congrArg (fun t : Fin (boundaryIdentity s).length =>
      (boundaryIdentity s)[t].1.2) hidx
    exact hlabel.symm.trans hi
  let d0 := discAt (markedRows rows w) (boundaryIdentity s) idx
    ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  have hcyc : P.rotation.SameCycle
      (discAt (markedRows rows w) (boundaryIdentity s) idx k) d0 := by
    change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle _ _
    rw [disc_sameCycle_iff]
    simp only [d0, discOccurrence_at]
  have hc0 : P.SameComponent z d0 :=
    Relation.EqvGen.trans _ _ _ hc (P.component_of_vertexCycle hcyc)
  have hd0 : ¬ P.rotation.SameCycle z d0 :=
    fun h => hd (h.trans hcyc.symm)
  let e : {d // P.SameComponent z d} := ⟨d0,hc0⟩
  refine ⟨e,i,?_,?_,hj,?_⟩
  · intro h
    apply hd0
    exact (P.restrict_sameVertex_iff (P.SameComponent z)
      (P.component_membership_edge z) (P.component_membership_rotation z)
      ⟨z, Relation.EqvGen.refl z⟩ e).mp h
  · change (boundaryIdentity s)[discOccurrence (markedRows rows w)
      (boundaryIdentity s) d0].1.2 = some i
    have hidx := discOccurrence_at (markedRows rows w) (boundaryIdentity s) idx
      ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    have hlabel := congrArg (fun t : Fin (boundaryIdentity s).length =>
      (boundaryIdentity s)[t].1.2) hidx
    exact hlabel.trans hi'
  · have hrow : rows i ≠ [] := by
      intro hnil
      have hpos : 0 < (orientedWord
          (markedRows rows w (boundaryIdentity s)[idx].1.2)
          (boundaryIdentity s)[idx].2).length := Nat.zero_lt_of_lt k.isLt
      rw [orientedWord_length, hi'] at hpos
      simp [markedRows, hnil] at hpos
    change 5 * (2 + 2 * 10^80) <
      4 * rawWeight (((P.componentRibbon z).vertexBoundary e).map (fun d => read d.val))
    rw [component_vertex_read]
    change 5 * (2 + 2 * 10^80) <
      4 * rawWeight (((boundaryRibbon rows w s hs).vertexBoundary d0).map read)
    rw [show d0 = discAt (markedRows rows w) (boundaryIdentity s) idx
      ⟨0, Nat.zero_lt_of_lt k.isLt⟩ from rfl]
    change 5 * (2 + 2 * 10^80) <
      4 * rawWeight (((boundaryRibbon rows w s hs).vertexBoundary
        (discAt (markedRows rows w) (boundaryIdentity s) idx
          ⟨0, Nat.zero_lt_of_lt k.isLt⟩)).map
        (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)))
    rw [boundaryRibbon_interior_read rows w s hs idx i hi' (Nat.zero_lt_of_lt k.isLt),
      orientedWord_rawWeight]
    exact guba_rankHeightRows_large pick n i hrow

#print axioms guba_boundary_component_large_row


/-! ## An actual coefficient region crossing the marked boundary

Splitting every non-coefficient vertex into singletons gives actual
lower-rank regions. If there is another non-coefficient vertex in the
marked component, at least one such region meets both the marked
vertex and a different non-coefficient vertex. This supplies an
incidence of the desired contiguity system, but neither the number
of outlets of that region nor its metric coverage is controlled here.
-/

/-- Some coefficient region must cross the marked vertex: otherwise
the union of regions meeting that vertex would be closed under both
permutations of the original ribbon. No planarity is needed for this
connectivity assertion. -/
theorem coefficient_region_crosses_vertex {D : Type} (P : RibbonMap D)
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (z b : D) (hc : P.SameComponent z b)
    (hb : ¬ keep b) (hzb : ¬ P.rotation.SameCycle z b)
    (hz : ∀ a, P.rotation.SameCycle z a → ¬ keep a) :
    ∃ a d, P.rotation.SameCycle z a ∧ ¬ keep a ∧ ¬ keep d ∧
      ¬ P.rotation.SameCycle z d ∧
      (P.coefficientRegions keep hkeep).SameComponent a d := by
  classical
  let S := P.coefficientRegions keep hkeep
  let reach : D → Prop := fun d =>
    ∃ a, P.rotation.SameCycle z a ∧ S.SameComponent a d
  by_contra hn
  have hper {d : D} (hd : ¬ keep d) :
      reach d ↔ P.rotation.SameCycle z d := by
    constructor
    · rintro ⟨a,ha,had⟩
      by_contra h
      exact hn ⟨a,d,ha,hz a ha,hd,h,had⟩
    · intro h
      exact ⟨d,h,Relation.EqvGen.refl d⟩
  have hmove {d e : D} (h : S.SameComponent d e) :
      reach e ↔ reach d := by
    constructor
    · rintro ⟨a,ha,hae⟩
      exact ⟨a,ha,Relation.EqvGen.trans _ _ _ hae
        (Relation.EqvGen.symm _ _ h)⟩
    · rintro ⟨a,ha,had⟩
      exact ⟨a,ha,Relation.EqvGen.trans _ _ _ had h⟩
  have hedge (d : D) : reach (P.edge d) ↔ reach d := by
    exact hmove (S.component_edge d)
  have hrot (d : D) : reach (P.rotation d) ↔ reach d := by
    by_cases hd : keep d
    · have he : S.rotation d = P.rotation d := by
        rw [show S = P.coefficientRegions keep hkeep from rfl,
          RibbonMap.coefficientRegions_rotation, ite_eq_left hd]
      rw [← he]
      exact hmove (S.component_rotation d)
    · rw [hper (fun h => hd ((hkeep d).mp h)), hper hd]
      exact Equiv.Perm.sameCycle_apply_right
  have hreach : reach b := (P.invariant_on_component reach hedge hrot hc).mp
    ⟨z,.refl _ _,Relation.EqvGen.refl z⟩
  exact hzb ((hper hb).mp hreach)

/-- For a word first killed at the last available rank, a genuine
lower-rank region connects a dart of the outer boundary to a dart
of a last-rank relator vertex. -/
theorem rankRibbon_outer_region_has_top_outlet (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X (j+1) i)) s = w)
    (hw : w ≠ 1) (hnew : w ∉ weightedHeightStage pick X j) :
    let rows := rankHeightRows pick X (j+1)
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let keep := lowerRankDart pick X (j+1) j w s
    ∃ hkeep : ∀ d, keep (P.rotation d) ↔ keep d,
      ∃ (a d : DiscDarts (markedRows rows w) (boundaryIdentity s))
        (i : RankHeight (j+1)),
        P.rotation.SameCycle z a ∧ ¬ P.rotation.SameCycle z d ∧
        (P.coefficientRegions keep hkeep).SameComponent a d ∧
        (boundaryIdentity s)[discOccurrence (markedRows rows w)
          (boundaryIdentity s) d].1.2 = some i ∧ i.1.val = j := by
  classical
  intro rows P z keep
  have hkeep : ∀ d, keep (P.rotation d) ↔ keep d := by
    intro d
    exact lowerRankDart_sameCycle pick X (j+1) j w s hs (P.rotation d) d
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  have hz : ¬ keep z := by
    rintro ⟨i,hi,_⟩
    change (boundaryIdentity s)[discOccurrence (markedRows rows w)
      (boundaryIdentity s) (boundaryDart rows w s hw)].1.2 = some i at hi
    have hidx := boundaryDart_occurrence rows w s hw
    have hlabel := congrArg (fun k : Fin (boundaryIdentity s).length =>
      (boundaryIdentity s)[k].1.2) hidx
    have hnone : (boundaryIdentity s)[boundaryOccurrence s].1.2 = none := rfl
    have habs : some i = none := hi.symm.trans (hlabel.trans hnone)
    cases habs
  obtain ⟨b,i,hc,hn,hi,hj⟩ := rankRibbon_boundary_component_has_high_cell
    pick X (j+1) j w s hs hw hnew
  have hb : ¬ keep b := by
    rintro ⟨i',hi',hlt⟩
    have he : i = i' := Option.some.inj (hi.symm.trans hi')
    rw [← he] at hlt
    omega
  obtain ⟨a,d,ha,_,hd,hnd,hreg⟩ :=
    coefficient_region_crosses_vertex P keep hkeep z b hc hb hn
      (fun a ha => fun h => hz ((lowerRankDart_sameCycle pick X
        (j+1) j w s hs z a ha).mpr h))
  have hk : discOccurrence (markedRows rows w) (boundaryIdentity s) d ≠
      boundaryOccurrence s := by
    intro he
    exact hnd ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr he)
  have hinterior (k : Fin (boundaryIdentity s).length)
      (hk' : k ≠ boundaryOccurrence s) :
      ∃ i : RankHeight (j+1), (boundaryIdentity s)[k].1.2 = some i := by
    obtain ⟨v,hv⟩ := k
    cases v with
    | zero => exact (hk' (Fin.ext rfl)).elim
    | succ m =>
      have hm : m < s.length := by simpa [boundaryIdentity] using hv
      refine ⟨s[m].1.2,?_⟩
      simp [boundaryIdentity,markOccurrence]
  obtain ⟨i',hi'⟩ := hinterior _ hk
  have hge : j ≤ i'.1.val := by
    by_contra! hlt
    exact hd ⟨i',hi',hlt⟩
  have heq : i'.1.val = j := by
    have hlt := i'.1.isLt
    omega
  exact ⟨hkeep,a,d,i',ha,hnd,hreg,hi',heq⟩

#print axioms coefficient_region_crosses_vertex
#print axioms rankRibbon_outer_region_has_top_outlet


/-! ## Peripheral weight before the first failure of the commutator

At the preceding rank neither generator is trivial. Therefore none
of the four signed letters is trivial in that quotient. Every
coefficient region incident to the periphery has at least two
outlets, and their disjoint supports account for the full peripheral
weight. This is an incidence partition, not yet a contiguity system:
regions with three or more outlets and repeated incidences on a
single peripheral vertex still have to be controlled.
-/

/-- Survival of the free-group commutator implies survival of every
signed generator. -/
theorem signed_letter_survives_of_commWord (N : Subgroup F) [N.Normal]
    (hcomm : commWord ∉ N) (x : Letter) : FreeGroup.mk [x] ∉ N := by
  have ha : a ∉ N := by
    intro h
    apply hcomm
    apply (QuotientGroup.eq_one_iff _).mp
    have hqa : QuotientGroup.mk' N a = 1 := (QuotientGroup.eq_one_iff _).mpr h
    change QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1
    simp only [map_mul, map_inv, hqa]
    group
  have hb : b ∉ N := by
    intro h
    apply hcomm
    apply (QuotientGroup.eq_one_iff _).mp
    have hqb : QuotientGroup.mk' N b = 1 := (QuotientGroup.eq_one_iff _).mpr h
    change QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1
    simp only [map_mul, map_inv, hqb]
    group
  have hg (i : Fin 2) : FreeGroup.of i ∉ N := by
    fin_cases i
    · exact ha
    · exact hb
  obtain ⟨i,sg⟩ := x
  intro hx
  cases sg with
  | false =>
    rw [FreeGroup.mk_eq_inv_of] at hx
    exact hg i (by simpa only [inv_inv] using N.inv_mem hx)
  | true =>
    rw [FreeGroup.mk_eq_of] at hx
    exact hg i hx

/-- Partition every non-lower-rank incidence by its actual coefficient
region. All summands have at least two outlets, with no weight lost.
The only survival premise is at the preceding rank, as available in
an induction on the first failure of the commutator. -/
theorem rankRibbon_outlet_weight_partition (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (hcomm : commWord ∉ weightedHeightStage pick X j) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let keep := lowerRankDart pick X n j w s
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let weight := fun d => letterWeight (read d)
    ∃ hkeep : ∀ d, keep (P.rotation d) ↔ keep d,
      let S := P.coefficientRegions keep hkeep
      ∃ (B R : Finset (DiscDarts (markedRows rows w) (boundaryIdentity s))),
        (∀ d, d ∈ B ↔ ¬ keep d) ∧ R ⊆ B ∧
        Set.PairwiseDisjoint (↑R : Set _) (guba22_component_support S B) ∧
        (∀ a ∈ R, 2 ≤ (guba22_component_support S B a).card) ∧
        (∑ a ∈ R, ∑ d ∈ guba22_component_support S B a, weight d) =
          ∑ d ∈ B, weight d := by
  classical
  intro rows P keep read weight
  obtain ⟨hkeep,hout⟩ := rankRibbon_lower_regions_no_unique_outlet pick X n j w s hs
  let S := P.coefficientRegions keep hkeep
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  let B := Finset.univ.filter (fun d => ¬ keep d)
  have hB (d) : d ∈ B ↔ ¬ keep d := by simp [B]
  obtain ⟨R,hsub,hdis,hsum⟩ := guba22_component_partition_weight S B weight
  refine ⟨hkeep,B,R,hB,hsub,hdis,?_,hsum⟩
  intro a ha
  have haB := hsub ha
  have hka := (hB a).mp haB
  obtain ⟨b,hab,hkb,hba⟩ := hout a hka
    (signed_letter_survives_of_commWord N hcomm (read a))
  have hbB := (hB b).mpr hkb
  have hpair : ({a,b} : Finset _) ⊆ guba22_component_support S B a := by
    intro d hd
    rcases Finset.mem_insert.mp hd with hda | hd
    · subst d
      exact (guba22_mem_component_support S B a a).mpr
        ⟨haB,Relation.EqvGen.refl a⟩
    · have he := Finset.mem_singleton.mp hd
      subst d
      exact (guba22_mem_component_support S B a b).mpr ⟨hbB,hab⟩
  calc
    2 = ({a,b} : Finset _).card := by simp [Ne.symm hba]
    _ ≤ (guba22_component_support S B a).card := Finset.card_le_card hpair

#print axioms signed_letter_survives_of_commWord
#print axioms rankRibbon_outlet_weight_partition


/-! ## Normalized edge weights used in Guba's Lemmas 10--19

The weighted length of a row is not the weight used in Lemma 19:
an incidence on a perimeter P receives its length divided by the
cube root of P. The following identities are on literal dart lists.
The transfer lemma isolates the metric step of Lemmas 10 and 17,
without postulating the existence of a preferred contiguity system.
-/

noncomputable def guba19Weight (perimeter : ℝ) (u : RawWord) : ℝ :=
  (rawWeight u : ℝ) / perimeter ^ (1/3 : ℝ)

theorem guba19Weight_append (p : ℝ) (u v : RawWord) :
    guba19Weight p (u ++ v) = guba19Weight p u + guba19Weight p v := by
  simp only [guba19Weight, rawWeight_append, Nat.cast_add, add_div]

theorem guba19Weight_map_sum {D : Type} (read : D → Letter)
    (p : ℝ) (ds : List D) :
    guba19Weight p (ds.map read) =
      (ds.map (fun d => guba19Weight p [read d])).sum := by
  induction ds with
  | nil => simp [guba19Weight, rawWeight]
  | cons d ds ih =>
    change guba19Weight p ([read d] ++ ds.map read) =
      guba19Weight p [read d] +
        (ds.map (fun e => guba19Weight p [read e])).sum
    rw [guba19Weight_append, ih]

/-- The sum over the complete perimeter is P^(2/3), with the same
normalization as in Guba's weight accounting. -/
theorem guba19Weight_total (u : RawWord) :
    guba19Weight (rawWeight u : ℝ) u = (rawWeight u : ℝ) ^ (2/3 : ℝ) := by
  by_cases h : rawWeight u = 0
  · simp [guba19Weight, h, Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0)]
  · have hp : 0 < (rawWeight u : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    calc
      _ = (rawWeight u : ℝ) ^ (1 : ℝ) /
          (rawWeight u : ℝ) ^ (1/3 : ℝ) := by rw [Real.rpow_one]; rfl
      _ = (rawWeight u : ℝ) ^ (1 - 1/3 : ℝ) :=
        (Real.rpow_sub hp 1 (1/3)).symm
      _ = _ := by congr 1; norm_num

/-- Exact normalized weight identity for an actual vertex of a ribbon. -/
theorem guba19_vertex_weight {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (d : D) :
    let ds := P.vertexBoundary d
    let p : ℝ := rawWeight (ds.map read)
    (ds.map (fun e => guba19Weight p [read e])).sum = p ^ (2/3 : ℝ) := by
  intro ds p
  rw [← guba19Weight_map_sum read p ds]
  exact guba19Weight_total (ds.map read)

/-- Transfer of normalized weights between two literal arc readings.
If P <= c^3 Q and the target length is at most twice the source
length, its normalized weight is at most 2c times the source
weight. Taking c = sqrt omega gives the metric step of Lemma 17.
The perimeter separation and length comparison are separate
geometric obligations, not assertions proved here. -/
theorem guba19_normalized_transfer (P Q c : ℝ) (u v : RawWord)
    (hp : 0 < P) (hq : 0 < Q) (hc : 0 < c)
    (hscale : P ≤ c^3 * Q) (hlen : rawWeight v ≤ 2 * rawWeight u) :
    guba19Weight Q v ≤ 2 * c * guba19Weight P u := by
  have hcub : (c^3) ^ (1/3 : ℝ) = c := by
    rw [← Real.rpow_natCast_mul hc.le 3 (1/3 : ℝ)]
    norm_num
  have hroot := Real.rpow_le_rpow hp.le hscale (by norm_num : 0 ≤ (1/3 : ℝ))
  rw [Real.mul_rpow (by positivity : 0 ≤ c^3) hq.le, hcub] at hroot
  have hp' := Real.rpow_pos_of_pos hp (1/3 : ℝ)
  have hq' := Real.rpow_pos_of_pos hq (1/3 : ℝ)
  have hl : (rawWeight v : ℝ) ≤ 2 * (rawWeight u : ℝ) := by exact_mod_cast hlen
  unfold guba19Weight
  calc
    (rawWeight v : ℝ) / Q ^ (1/3 : ℝ) ≤
        (2 * (rawWeight u : ℝ)) / Q ^ (1/3 : ℝ) :=
      div_le_div_of_nonneg_right hl hq'.le
    _ ≤ (2 * c * (rawWeight u : ℝ)) / P ^ (1/3 : ℝ) := by
      apply (div_le_div_iff₀ hq' hp').mpr
      calc
        _ ≤ (2 * (rawWeight u : ℝ)) * (c * Q ^ (1/3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
        _ = _ := by ring
    _ = _ := by ring

#print axioms guba19Weight
#print axioms guba19Weight_append
#print axioms guba19Weight_map_sum
#print axioms guba19Weight_total
#print axioms guba19_vertex_weight
#print axioms guba19_normalized_transfer


/-! ## Numerical conclusion of Lemma 19

The nine-category accounting in Guba gives the single inequality
haccount below (Math. USSR Izvestiya 29 (1987), p. 253).
The following theorem proves its exact numerical consequence with
the original constants. It does not assert that arbitrary ribbons
satisfy haccount; that is the remaining geometric obligation.
-/

theorem guba19_outer_weight_arithmetic (V M N : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (htotal : V = M + N)
    (haccount : M ≤ V * (1 - 99/100 + 4000*(1/10^7) +
      450*(1/10^17 : ℝ)^(1/2 : ℝ) +
      300*(1/10^11 : ℝ)^(1/2 : ℝ)) +
      (8/15 + 2*(1/10^7 : ℝ)^(1/2 : ℝ))*M) :
    (95/100 + 300*(1/10^7 : ℝ)^(3/2 : ℝ))*V ≤ N := by
  have root_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hxy : x ≤ y^2) : x^(1/2 : ℝ) ≤ y := by
    have h := Real.rpow_le_rpow hx hxy (by norm_num : 0 ≤ (1/2 : ℝ))
    rw [← Real.rpow_natCast_mul hy 2 (1/2 : ℝ)] at h
    norm_num at h
    exact h
  have hw : (1/10^7 : ℝ)^(1/2 : ℝ) ≤ 1/1000 :=
    root_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have hb : (1/10^17 : ℝ)^(1/2 : ℝ) ≤ 1/10^8 :=
    root_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have ht : (1/10^11 : ℝ)^(1/2 : ℝ) ≤ 1/200000 :=
    root_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have hV : 0 ≤ V := by linarith
  have hc : 1 - 99/100 + 4000*(1/10^7) +
      450*(1/10^17 : ℝ)^(1/2 : ℝ) +
      300*(1/10^11 : ℝ)^(1/2 : ℝ) ≤ (1/75 : ℝ) := by
    linarith only [hb,ht]
  have hd : 8/15 + 2*(1/10^7 : ℝ)^(1/2 : ℝ) ≤ (2/3 : ℝ) := by
    linarith only [hw]
  have he : M ≤ V*(1/75) + (2/3)*M :=
    haccount.trans (add_le_add (mul_le_mul_of_nonneg_left hc hV)
      (mul_le_mul_of_nonneg_right hd hM))
  have houter : (96/100 : ℝ)*V ≤ N := by linarith only [he,htotal]
  have hpow : (1/10^7 : ℝ)^(3/2 : ℝ) =
      (1/10^7 : ℝ) * (1/10^7 : ℝ)^(1/2 : ℝ) := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add (by norm_num : 0 < (1/10^7 : ℝ)), Real.rpow_one]
  have htarget : (95/100 + 300*(1/10^7 : ℝ)^(3/2 : ℝ)) ≤ 96/100 := by
    rw [hpow]
    linarith only [hw]
  exact (mul_le_mul_of_nonneg_right htarget hV).trans houter

#print axioms guba19_outer_weight_arithmetic


/-! ## Two full peripheral readings through a lower-rank region

Unlike the direct-edge splicing lemma, the two marked vertices may
be separated by arbitrarily many interior vertices. Work in their
actual connected component and retain their full literal readings.
-/

/-- The two marked vertex readings in any spherical component
are inverse conjugate modulo the normal subgroup killing the other
vertices. No direct edge between the marked vertices is required. -/
theorem component_two_boundary_inverse_conjugacy {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hE : P.EulerEquality) (a b : D)
    (hab : P.SameComponent a b) (hne : ¬ P.rotation.SameCycle a b)
    (hint : ∀ d, P.SameComponent a d → ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N) :
    ∃ g : F ⧸ N,
      QuotientGroup.mk' N (FreeGroup.mk ((P.vertexBoundary a).map read)) * g *
        QuotientGroup.mk' N (FreeGroup.mk ((P.vertexBoundary b).map read)) * g⁻¹ = 1 := by
  classical
  let C := P.componentRibbon a
  let q := QuotientGroup.mk' N
  let x : {d : D // P.SameComponent a d} := ⟨a,Relation.EqvGen.refl a⟩
  let y : {d : D // P.SameComponent a d} := ⟨b,hab⟩
  let v : {d : D // P.SameComponent a d} → F ⧸ N :=
    fun d => q (FreeGroup.mk [read d.val])
  have hEC : C.EulerEquality := by
    change Fintype.card (P.componentRibbon a).Vertex +
      Fintype.card (P.componentRibbon a).Face =
      Fintype.card (P.componentRibbon a).Edge +
        2 * Fintype.card (P.componentRibbon a).Component
    rw [P.componentRibbon_card_components, mul_one]
    exact P.componentRibbon_sphere hE a
  have hxy : ¬ C.rotation.SameCycle x y := by
    intro h
    exact hne ((P.restrict_sameVertex_iff (P.SameComponent a)
      (P.component_membership_edge a) (P.component_membership_rotation a) x y).mp h)
  have eval (ds : List {d : D // P.SameComponent a d}) :
      (ds.map v).prod = q (FreeGroup.mk (ds.map (fun d => read d.val))) := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons d ds ih =>
      change v d * (ds.map v).prod =
        q (FreeGroup.mk ([read d.val] ++ ds.map (fun e => read e.val)))
      rw [ih, ← FreeGroup.mul_mk, map_mul]
  have hread (d : {d : D // P.SameComponent a d}) :
      cycleProduct C.rotation v d =
        q (FreeGroup.mk ((P.vertexBoundary d.val).map read)) := by
    change ((C.vertexBoundary d).map v).prod = _
    rw [eval, component_vertex_read P read a d]
  obtain ⟨g,hg⟩ := guba22_two_boundary_product C v
    (by
      intro d
      change q (FreeGroup.mk [read (P.edge d.val)]) =
        (q (FreeGroup.mk [read d.val]))⁻¹
      rw [he, signedLetterValue_reverse, map_inv])
    (P.componentRibbon_connected a) hEC x y hxy (by
      intro d hdx hdy
      rw [hread]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hint d.val d.property
      · intro h
        exact hdx ((P.restrict_sameVertex_iff (P.SameComponent a)
          (P.component_membership_edge a) (P.component_membership_rotation a) x d).mpr h)
      · intro h
        exact hdy ((P.restrict_sameVertex_iff (P.SameComponent a)
          (P.component_membership_edge a) (P.component_membership_rotation a) y d).mpr h))
  rw [hread x, hread y] at hg
  exact ⟨g,hg⟩

/-- Arbitrary protected cuts of an actual rank ribbon preserve
the lower-rank cells. If a component of the refinement has just
two peripheral interval vertices, their full words are inverse
conjugate modulo the earlier presentation. The existence and
size of such a component must still be established geometrically. -/
theorem rankRibbon_protected_two_arc_conjugacy (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (cuts : List ((DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s)) × (DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s)))) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let keep := lowerRankDart pick X n j w s
    let S := cuts.foldl (fun Q x => Q.vertexCut x.1 x.2) P
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∀ a b, (∀ x ∈ cuts, ¬keep x.1 ∧ ¬keep x.2) →
      SplitRefinement P.rotation S.rotation →
      (P.withRotation S.rotation).SameComponent a b → ¬ S.rotation.SameCycle a b →
      (∀ d, (P.withRotation S.rotation).SameComponent a d → ¬ S.rotation.SameCycle a d →
        ¬ S.rotation.SameCycle b d → keep d) →
      ∃ g : F,
        FreeGroup.mk (((P.withRotation S.rotation).vertexBoundary a).map read) * g *
        FreeGroup.mk (((P.withRotation S.rotation).vertexBoundary b).map read) * g⁻¹ ∈
          weightedHeightStage pick X j := by
  classical
  intro rows P keep S read a b hout href hab hne hint
  have hkeep : ∀ d, keep (P.rotation d) ↔ keep d := by
    intro d
    exact lowerRankDart_sameCycle pick X n j w s hs (P.rotation d) d
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  have hag := (protected_splitRefinement_agreement P keep hkeep cuts hout).2
  have hE : P.EulerEquality := boundaryRibbon_euler rows w s hs
  let T := P.withRotation S.rotation
  have hET : T.EulerEquality := P.splitRefinement_preserves_euler href hE
  let N := weightedHeightStage pick X j
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  have he : ∀ d, read (T.edge d) = reverseLetter (read d) :=
    relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
      (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs)
  have hinside : ∀ d, T.SameComponent a d → ¬ T.rotation.SameCycle a d →
      ¬ T.rotation.SameCycle b d → FreeGroup.mk ((T.vertexBoundary d).map read) ∈ N := by
    intro d hc hd1 hd2
    have hd := hint d hc hd1 hd2
    have hrot : ∀ e, P.rotation.SameCycle d e → S.rotation e = P.rotation e :=
      fun e he => hag e ((lowerRankDart_sameCycle pick X n j w s hs d e he).mp hd)
    change FreeGroup.mk (((P.withRotation S.rotation).vertexBoundary d).map read) ∈
      weightedHeightStage pick X j
    rw [refined_vertex_read_of_agreement P S.rotation d hrot]
    obtain ⟨i,hi,hlt⟩ := hd
    exact rankRibbon_lower_vertex_mem pick X n j w s hs d i hi hlt
  obtain ⟨g,hg⟩ := component_two_boundary_inverse_conjugacy T read N he hET a b hab hne hinside
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N g
  refine ⟨u,(QuotientGroup.eq_one_iff _).mp ?_⟩
  change QuotientGroup.mk' N (FreeGroup.mk ((T.vertexBoundary a).map read) * u *
    FreeGroup.mk ((T.vertexBoundary b).map read) * u⁻¹) = 1
  simpa only [map_mul, map_inv] using hg

#print axioms component_two_boundary_inverse_conjugacy
#print axioms rankRibbon_protected_two_arc_conjugacy


/-! ## Global normalized perimeter accounting

Use the actual vertex quotient and its literal rotation cycles.
This is a change of summation index, not a small-cancellation
estimate. In particular no incidence is duplicated or omitted.
-/

/-- The vertex perimeter is independent of the corner chosen to
read its rotation cycle. -/
theorem ribbon_perimeter_sameCycle {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a b : D)
    (hab : P.rotation.SameCycle a b) :
    rawWeight ((P.vertexBoundary a).map read) =
      rawWeight ((P.vertexBoundary b).map read) := by
  classical
  have eval (ds : List D) :
      rawWeight (ds.map read) = (ds.map (fun d => letterWeight (read d))).sum := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      change letterWeight (read d) + rawWeight (ds.map read) =
        letterWeight (read d) + (ds.map (fun d => letterWeight (read d))).sum
      rw [ih]
  have hsets : (P.vertexBoundary a).toFinset = (P.vertexBoundary b).toFinset := by
    ext d
    simp only [List.mem_toFinset, P.mem_vertexBoundary_iff]
    exact ⟨fun h => hab.symm.trans h, fun h => hab.trans h⟩
  rw [eval, eval, ← List.sum_toFinset _ (P.vertexBoundary_nodup a),
    ← List.sum_toFinset _ (P.vertexBoundary_nodup b), hsets]

/-- The perimeter function descends to the actual quotient of darts
by the vertex rotation cycles. -/
noncomputable def ribbonVertexPerimeter {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) : P.Vertex → ℕ :=
  Quotient.lift (fun d => rawWeight ((P.vertexBoundary d).map read))
    (fun a b h => ribbon_perimeter_sameCycle P read a b h)

theorem ribbonVertexPerimeter_at {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (d : D) :
    ribbonVertexPerimeter P read (P.vertexOf d) =
      rawWeight ((P.vertexBoundary d).map read) := rfl

/-- Summing P^(2/3) over every actual vertex counts precisely the
normalized weights of all darts. This includes the marked boundary
vertex if the ribbon has one; it does not yet distinguish internal
from external contiguity edges. -/
theorem guba19_total_vertex_dart_weight {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) :
    (∑ v : P.Vertex, (ribbonVertexPerimeter P read v : ℝ) ^ (2/3 : ℝ)) =
      ∑ d : D, guba19Weight (ribbonVertexPerimeter P read (P.vertexOf d) : ℝ) [read d] := by
  classical
  let weight : D → ℝ := fun d =>
    guba19Weight (ribbonVertexPerimeter P read (P.vertexOf d) : ℝ) [read d]
  change _ = ∑ d : D, weight d
  rw [← Finset.sum_fiberwise Finset.univ P.vertexOf weight]
  apply Finset.sum_congr rfl
  intro v _
  obtain ⟨a,rfl⟩ := Quotient.exists_rep v
  change (ribbonVertexPerimeter P read (P.vertexOf a) : ℝ) ^ (2/3 : ℝ) =
    ∑ d ∈ Finset.univ.filter (fun d => P.vertexOf d = P.vertexOf a), weight d
  have hset : Finset.univ.filter (fun d => P.vertexOf d = P.vertexOf a) =
      (P.vertexBoundary a).toFinset := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
      P.mem_vertexBoundary_iff]
    exact ⟨fun h => (Quotient.exact h).symm, fun h => Quotient.sound h.symm⟩
  rw [hset, ribbonVertexPerimeter_at]
  calc
    _ = ((P.vertexBoundary a).map (fun d =>
        guba19Weight (rawWeight ((P.vertexBoundary a).map read) : ℝ) [read d])).sum :=
      (guba19_vertex_weight P read a).symm
    _ = ∑ d ∈ (P.vertexBoundary a).toFinset, weight d := by
      rw [← List.sum_toFinset _ (P.vertexBoundary_nodup a)]
      apply Finset.sum_congr rfl
      intro d hd
      have hcyc := (P.mem_vertexBoundary_iff a d).mp (List.mem_toFinset.mp hd)
      simp only [weight, ribbonVertexPerimeter_at]
      rw [ribbon_perimeter_sameCycle P read a d hcyc]

#print axioms ribbon_perimeter_sameCycle
#print axioms ribbonVertexPerimeter
#print axioms ribbonVertexPerimeter_at
#print axioms guba19_total_vertex_dart_weight


/-! ## Exact edge accounting on a ribbon

Every geometric edge has two actual incidence darts. The endpoint
weights can differ because of the different perimeter denominators.
Their sum is well defined on the edge quotient, even for loops.
-/

/-- Sum of the endpoint weights of a geometric edge. -/
noncomputable def ribbonEdgeWeight {D : Type} [Fintype D]
    (P : RibbonMap D) (weight : D → ℝ) : P.Edge → ℝ :=
  Quotient.lift (fun d => weight d + weight (P.edge d)) (by
    intro a b hab
    rcases (P.edge_sameCycle_iff a b).mp hab with rfl | h
    · rfl
    · rw [h, P.edge_involutive, add_comm])

theorem ribbonEdgeWeight_at {D : Type} [Fintype D]
    (P : RibbonMap D) (weight : D → ℝ) (d : D) :
    ribbonEdgeWeight P weight (P.edgeOf d) = weight d + weight (P.edge d) := rfl

/-- The exact sum over geometric edges equals the sum over darts:
both ends are included once, including at loop edges. -/
theorem ribbon_total_edge_weight {D : Type} [Fintype D]
    (P : RibbonMap D) (weight : D → ℝ) :
    (∑ e : P.Edge, ribbonEdgeWeight P weight e) = ∑ d : D, weight d := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ P.edgeOf weight]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨d,rfl⟩ := Quotient.exists_rep e
  change ribbonEdgeWeight P weight (P.edgeOf d) =
    ∑ x ∈ Finset.univ.filter (fun x => P.edgeOf x = P.edgeOf d), weight x
  have hset : Finset.univ.filter (fun x => P.edgeOf x = P.edgeOf d) =
      {d, P.edge d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, P.edgeOf_eq_iff]
  rw [ribbonEdgeWeight_at, hset, Finset.sum_pair (Ne.symm (P.edge_ne d))]

/-- Both descriptions of the total normalized weight agree on the
actual ribbon; the geometric edges are not a hypothetical index set. -/
theorem guba19_total_vertex_edge_weight {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) :
    (∑ v : P.Vertex, (ribbonVertexPerimeter P read v : ℝ) ^ (2/3 : ℝ)) =
      ∑ e : P.Edge, ribbonEdgeWeight P
        (fun d => guba19Weight (ribbonVertexPerimeter P read (P.vertexOf d) : ℝ)
          [read d]) e := by
  rw [ribbon_total_edge_weight, guba19_total_vertex_dart_weight]

#print axioms ribbonEdgeWeight
#print axioms ribbonEdgeWeight_at
#print axioms ribbon_total_edge_weight
#print axioms guba19_total_vertex_edge_weight


/-! ## Contraction inside a coefficient region

Contract an actual edge whose two vertices are interior (below the
chosen rank). The surviving peripheral vertices must retain not
just their degree but their full ordered words. This is the local
surgery for compressing coefficient regions, with no assumption
about an abstract graph of contiguities.
-/

/-- A contraction between two distinct interior vertices cannot
identify a peripheral vertex with any other surviving vertex. -/
theorem contractEdge_peripheral_sameVertex {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (a : D) (ha : keep a) (ha' : keep (P.edge a))
    (hn : ¬ P.rotation.SameCycle a (P.edge a))
    (d e : P.ContractDart a) (hd : ¬ keep d.val) :
    (P.contractEdge a).rotation.SameCycle d e ↔ P.rotation.SameCycle d.val e.val := by
  rw [P.contractEdge_sameVertex_iff, P.edgeSplice_sameVertex_iff a hn]
  constructor
  · rintro (h | h)
    · exact h
    · rcases h.1 with hda | hda
      · exact (hd ((hkeep _ _ hda).mpr ha)).elim
      · exact (hd ((hkeep _ _ hda).mpr ha')).elim
  · exact Or.inl

/-- Contracting an interior edge preserves the exact cyclic list
of every peripheral vertex. The equality is of literal dart lists
under the canonical inclusion, not only of lengths or group values. -/
theorem contractEdge_peripheral_boundary {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (a : D) (ha : keep a) (ha' : keep (P.edge a))
    (d : P.ContractDart a) (hd : ¬ keep d.val) :
    ((P.contractEdge a).vertexBoundary d).map Subtype.val =
      P.vertexBoundary d.val := by
  classical
  have h1 : ¬ P.rotation.SameCycle d.val (P.rotation a) := by
    intro h
    have hda : P.rotation.SameCycle d.val a :=
      (Equiv.Perm.sameCycle_apply_right).mp h
    exact hd ((hkeep _ _ hda).mpr ha)
  have h2 : ¬ P.rotation.SameCycle d.val (P.edge a) :=
    fun h => hd ((hkeep _ _ h).mpr ha')
  have hs : (P.edgeSplice a).vertexBoundary d.val = P.vertexBoundary d.val :=
    cycleBoundary_cutAt_unchanged P.rotation (P.rotation a) (P.edge a) d.val h1 h2
  have hfilter := (P.spliceCancellation a).vertexBoundary_filter d
  change ((P.contractEdge a).vertexBoundary d).map Subtype.val =
    ((P.edgeSplice a).vertexBoundary d.val).filter
      (fun x => decide (x ≠ a ∧ x ≠ P.edge a)) at hfilter
  rw [hs] at hfilter
  rw [hfilter]
  apply List.filter_eq_self.mpr
  intro x hx
  have hxk : ¬ keep x := by
    intro hk
    exact hd ((hkeep _ _ ((P.mem_vertexBoundary_iff d.val x).mp hx)).mpr hk)
  exact decide_eq_true ⟨fun h => hxk (h ▸ ha), fun h => hxk (h ▸ ha')⟩

/-- The same operation preserves every peripheral word under any
letter labelling, hence also its raw and normalized weights. -/
theorem contractEdge_peripheral_read {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (a : D) (ha : keep a) (ha' : keep (P.edge a))
    (d : P.ContractDart a) (hd : ¬ keep d.val) :
    ((P.contractEdge a).vertexBoundary d).map (fun e => read e.val) =
      (P.vertexBoundary d.val).map read := by
  rw [← contractEdge_peripheral_boundary P keep hkeep a ha ha' d hd, List.map_map]
  rfl

/-- The transferred interior predicate is constant on contracted
vertices. Consequently the local surgery can be iterated without
losing the distinction between interior and peripheral vertices. -/
theorem contractEdge_keep_sameVertex {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (a : D) (ha : keep a) (ha' : keep (P.edge a))
    (hn : ¬ P.rotation.SameCycle a (P.edge a))
    (d e : P.ContractDart a)
    (h : (P.contractEdge a).rotation.SameCycle d e) :
    keep d.val ↔ keep e.val := by
  rw [P.contractEdge_sameVertex_iff, P.edgeSplice_sameVertex_iff a hn] at h
  rcases h with h | ⟨hd,he⟩
  · exact hkeep _ _ h
  · have hkd : keep d.val := by
      rcases hd with hd | hd
      · exact (hkeep _ _ hd).mpr ha
      · exact (hkeep _ _ hd).mpr ha'
    have hke : keep e.val := by
      rcases he with he | he
      · exact (hkeep _ _ he).mpr ha
      · exact (hkeep _ _ he).mpr ha'
    exact iff_of_true hkd hke

#print axioms contractEdge_peripheral_sameVertex
#print axioms contractEdge_peripheral_boundary
#print axioms contractEdge_peripheral_read
#print axioms contractEdge_keep_sameVertex


/-! ## Finite compression of interior edges

Iterate the actual edge contraction on strictly decreasing finite
dart types. All surviving edge pairings are inherited from the
original ribbon. Every original peripheral dart survives, and its
full ordered peripheral boundary survives as well. The terminal
condition only excludes non-loop edges between interior vertices:
deletion of interior loops and contiguity-band compression are
subsequent, distinct operations.
-/

theorem exists_interior_edge_compression {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D),
      Q.EulerEquality ∧ (P.Connected → Q.Connected) ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) →
        (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) ∧
      (∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e))) ∧
      (∀ d, keep (f d) → keep (f (Q.edge d)) →
        Q.rotation.SameCycle d (Q.edge d)) := by
  classical
  have main : ∀ (n : ℕ) (A : Type) [Fintype A] (R : RibbonMap A)
      (interior : A → Prop), Fintype.card A = n →
      (∀ d e, R.rotation.SameCycle d e → (interior d ↔ interior e)) →
      R.EulerEquality →
      ∃ (B : Type) (_ : Fintype B) (T : RibbonMap B) (j : B ↪ A),
        T.EulerEquality ∧ (R.Connected → T.Connected) ∧
        (∀ d, j (T.edge d) = R.edge (j d)) ∧
        (∀ d, ¬ interior d → ∃ e, j e = d) ∧
        (∀ d, ¬ interior (j d) →
          (T.vertexBoundary d).map j = R.vertexBoundary (j d)) ∧
        (∀ d e, T.rotation.SameCycle d e → (interior (j d) ↔ interior (j e))) ∧
        (∀ d, interior (j d) → interior (j (T.edge d)) →
          T.rotation.SameCycle d (T.edge d)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro A inst R interior hcard hinv heuler
      by_cases hex : ∃ a, interior a ∧ interior (R.edge a) ∧
          ¬ R.rotation.SameCycle a (R.edge a)
      · obtain ⟨a,ha,ha',hn⟩ := hex
        let U := R.contractEdge a
        let inc : R.ContractDart a ↪ A := ⟨Subtype.val,Subtype.val_injective⟩
        let inside : R.ContractDart a → Prop := fun d => interior d.val
        have hlt : Fintype.card (R.ContractDart a) < n := by
          have hh := R.contractEdge_card_darts a
          omega
        have hU : U.EulerEquality := R.contractEdge_euler a hn heuler
        have hI : ∀ d e, U.rotation.SameCycle d e → (inside d ↔ inside e) :=
          contractEdge_keep_sameVertex R interior hinv a ha ha' hn
        obtain ⟨B,instB,T,j,hT,hconn,hedge,hsurv,hread,hcycles,hterminal⟩ :=
          ih (Fintype.card (R.ContractDart a)) hlt (R.ContractDart a)
            U inside rfl hI hU
        let f : B ↪ A := j.trans inc
        refine ⟨B,instB,T,f,hT,?_,?_,?_,?_,?_,?_⟩
        · intro hc
          exact hconn (R.contractEdge_connected hc a hn)
        · intro d
          change (j (T.edge d)).val = R.edge (j d).val
          rw [hedge, R.contractEdge_edge_val a]
        · intro d hd
          let e : R.ContractDart a := ⟨d,fun h => hd (h ▸ ha),
            fun h => hd (h ▸ ha')⟩
          obtain ⟨b,hb⟩ := hsurv e hd
          exact ⟨b,congrArg Subtype.val hb⟩
        · intro d hd
          change (T.vertexBoundary d).map (fun b => (j b).val) =
            R.vertexBoundary (j d).val
          calc
            _ = ((T.vertexBoundary d).map j).map Subtype.val := by
              rw [List.map_map]
              rfl
            _ = (U.vertexBoundary (j d)).map Subtype.val :=
              congrArg (List.map Subtype.val) (hread d hd)
            _ = _ := contractEdge_peripheral_boundary R interior hinv a ha ha' (j d) hd
        · exact hcycles
        · exact hterminal
      · refine ⟨A,inst,R,Function.Embedding.refl A,heuler,
          fun h => h,fun _ => rfl,?_,?_,hinv,?_⟩
        · intro d _
          exact ⟨d,rfl⟩
        · intro d _
          exact List.map_id _
        · intro d hd hd'
          by_contra hn
          exact hex ⟨d,hd,hd',hn⟩
  exact main (Fintype.card D) D P keep rfl hkeep hE

#print axioms exists_interior_edge_compression


/-! ## Shape of compressed coefficient regions

After splitting the peripheral vertices into singleton incidences
and contracting all non-loop interior edges, each component that
contains an interior vertex has a single such vertex. Its peripheral
darts are leaves attached to this vertex. Interior loops may remain;
removing an arbitrary loop without tracking its separating faces
would not in general preserve the component.
-/

/-- In a terminal coefficient region with peripheral leaves, every
interior dart lies on the same vertex as any given interior dart
in its component, and every peripheral dart in that component is
attached to that vertex. -/
theorem compressed_region_star {D : Type} (P : RibbonMap D)
    (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hterminal : ∀ d, keep d → keep (P.edge d) →
      P.rotation.SameCycle d (P.edge d))
    (a : D) (ha : keep a) (b : D) (hab : P.SameComponent a b) :
    (keep b → P.rotation.SameCycle a b) ∧
      (¬ keep b → P.rotation.SameCycle a (P.edge b)) := by
  classical
  let reach : D → Prop := fun d =>
    P.rotation.SameCycle a d ∨
      (¬ keep d ∧ P.rotation.SameCycle a (P.edge d))
  have step (d : D) (hd : reach d) : reach (P.edge d) := by
    rcases hd with h | ⟨_,h⟩
    · by_cases hk : keep (P.edge d)
      · exact Or.inl (h.trans (hterminal d ((hkeep a d h).mp ha) hk))
      · exact Or.inr ⟨hk,by rw [P.edge_involutive]; exact h⟩
    · exact Or.inl h
  have hedge (d : D) : reach (P.edge d) ↔ reach d := by
    constructor
    · intro h
      have hh := step (P.edge d) h
      rwa [P.edge_involutive] at hh
    · exact step d
  have hrot (d : D) : reach (P.rotation d) ↔ reach d := by
    by_cases hd : keep d
    · have hcycle : P.rotation.SameCycle d (P.rotation d) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      have hr : keep (P.rotation d) := (hkeep _ _ hcycle).mp hd
      simp only [reach, hd, hr, not_true_eq_false, false_and, or_false,
        Equiv.Perm.sameCycle_apply_right]
    · rw [hleaf d hd]
  have hb : reach b := (P.invariant_on_component reach hedge hrot hab).mp
    (Or.inl (.refl _ _))
  constructor
  · intro hk
    rcases hb with h | h
    · exact h
    · exact (h.1 hk).elim
  · intro hk
    rcases hb with h | h
    · exact (hk ((hkeep a b h).mp ha)).elim
    · exact h.2

/-- A literal preserved peripheral singleton remains a singleton
vertex in the compressed ribbon. This bridges the finite
compression theorem to the star-shape argument. -/
theorem compressed_peripheral_leaf {D E : Type} [Fintype D] [Fintype E]
    (P : RibbonMap D) (Q : RibbonMap E) (f : E ↪ D) (keep : D → Prop)
    (hread : ∀ d, ¬ keep (f d) →
      (Q.vertexBoundary d).map f = P.vertexBoundary (f d))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (d : E) (hd : ¬ keep (f d)) : Q.rotation d = d := by
  have hcyc : Q.rotation.SameCycle d (Q.rotation d) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have hm : f (Q.rotation d) ∈ (Q.vertexBoundary d).map f :=
    List.mem_map.mpr ⟨_,(Q.mem_vertexBoundary_iff d _).mpr hcyc,rfl⟩
  rw [hread d hd, fixed_vertex_read_singleton P (f d) (hleaf _ hd)] at hm
  exact f.injective (List.mem_singleton.mp hm)

/-- Any component of a compressed coefficient ribbon containing an
interior vertex has the asserted star shape, with all peripheral
words and the Euler equation preserved. -/
theorem exists_coefficient_star_compression {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D),
      Q.EulerEquality ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) → Q.rotation d = d) ∧
      (∀ a b, Q.SameComponent a b → keep (f a) →
        (keep (f b) → Q.rotation.SameCycle a b) ∧
        (¬ keep (f b) → Q.rotation.SameCycle a (Q.edge b))) := by
  classical
  let S := P.coefficientRegions keep hkeep
  have hS : S.EulerEquality := P.coefficientRegions_euler keep hkeep hE
  have hinv : ∀ d e, S.rotation.SameCycle d e → (keep d ↔ keep e) := by
    intro d e h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    clear hn h
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hi (x : D) : keep (S.rotation x) ↔ keep x := by
        change keep ((P.coefficientRegions keep hkeep).rotation x) ↔ keep x
        rw [RibbonMap.coefficientRegions_rotation]
        split
        · exact hkeep x
        · rfl
      exact ih.trans (hi _).symm
  obtain ⟨E,inst,Q,f,hQ,_,hedge,hsurv,hread,hcycles,hterminal⟩ :=
    exists_interior_edge_compression S keep hinv hS
  have hleafS : ∀ d, ¬ keep d → S.rotation d = d := by
    intro d hd
    change (P.coefficientRegions keep hkeep).rotation d = d
    rw [RibbonMap.coefficientRegions_rotation, ite_eq_right hd]
  have hleafQ : ∀ d, ¬ keep (f d) → Q.rotation d = d :=
    compressed_peripheral_leaf S Q f keep hread hleafS
  refine ⟨E,inst,Q,f,hQ,hedge,hsurv,hleafQ,?_⟩
  intro a b hab ha
  exact compressed_region_star Q (fun d => keep (f d)) hcycles hleafQ
    hterminal a ha b hab

#print axioms compressed_region_star
#print axioms compressed_peripheral_leaf
#print axioms exists_coefficient_star_compression


/-! ## Coefficient regions without an interior vertex

If both ends of an edge are peripheral singleton vertices, its
connected component consists of exactly its two darts. This is the
other terminal possibility besides an interior star with loops.
-/

theorem peripheral_edge_component {D : Type} (P : RibbonMap D) (a b : D)
    (ha : P.rotation a = a)
    (he : P.rotation (P.edge a) = P.edge a) :
    P.SameComponent a b ↔ b = a ∨ b = P.edge a := by
  constructor
  · intro hab
    let reach : D → Prop := fun d => d = a ∨ d = P.edge a
    have step (d : D) (hd : reach d) : reach (P.edge d) := by
      rcases hd with h | h
      · exact Or.inr (congrArg P.edge h)
      · exact Or.inl ((congrArg P.edge h).trans (P.edge_involutive a))
    have hedge (d : D) : reach (P.edge d) ↔ reach d := by
      constructor
      · intro hd
        have hh := step (P.edge d) hd
        rwa [P.edge_involutive] at hh
      · exact step d
    have hrot (d : D) : reach (P.rotation d) ↔ reach d := by
      constructor
      · rintro (h | h)
        · exact Or.inl (P.rotation.injective (h.trans ha.symm))
        · exact Or.inr (P.rotation.injective (h.trans he.symm))
      · rintro (h | h)
        · exact Or.inl ((congrArg P.rotation h).trans ha)
        · exact Or.inr ((congrArg P.rotation h).trans he)
    exact (P.invariant_on_component reach hedge hrot hab).mp (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact P.component_edge a

/-- A peripheral dart either belongs to an isolated two-dart
edge or has an interior neighbor. This conclusion uses actual
edge pairings rather than a hypothetical contiguity graph. -/
theorem coefficient_peripheral_edge_or_interior {D : Type} (P : RibbonMap D)
    (keep : D → Prop) (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (a : D) (ha : ¬ keep a) :
    (¬ keep (P.edge a) ∧ ∀ b, P.SameComponent a b ↔ b = a ∨ b = P.edge a) ∨
      keep (P.edge a) := by
  classical
  by_cases h : keep (P.edge a)
  · exact Or.inr h
  · exact Or.inl ⟨h,fun b => peripheral_edge_component P a b (hleaf a ha) (hleaf _ h)⟩

#print axioms peripheral_edge_component
#print axioms coefficient_peripheral_edge_or_interior



/-! ## Face walks of loop-free compressed coefficient regions

The terminal stars become literal one-face components once their
interior loops are absent. This is proved directly with the face
permutation, without any graph-theoretic planarity assumption.
The removal of separating interior loops is a separate obligation.
-/

/-- Traversing an edge with a singleton endpoint stays on the same face. -/
theorem face_sameCycle_of_fixed_edge_endpoint {D : Type}
    (P : RibbonMap D) (d : D)
    (h : P.rotation d = d ∨ P.rotation (P.edge d) = P.edge d) :
    P.face.SameCycle d (P.edge d) := by
  have next (x : D) : P.face.SameCycle x (P.face x) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  rcases h with hd | he
  · have hf : P.face (P.edge d) = d := by
      apply P.rotation.injective
      rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
      exact (P.edge_involutive d).trans hd.symm
    have hh := next (P.edge d)
    rw [hf] at hh
    exact hh.symm
  · have hf : P.face d = P.edge d := by
      apply P.rotation.injective
      simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using he.symm
    rw [← hf]
    exact next d

/-- If every edge has a singleton endpoint, a whole connected component
is traversed by one face cycle. This applies both to isolated
peripheral edges and to compressed stars without interior loops. -/
theorem face_sameCycle_of_fixed_edge_endpoints {D : Type}
    (P : RibbonMap D)
    (h : ∀ d, P.rotation d = d ∨ P.rotation (P.edge d) = P.edge d)
    (a b : D) (hab : P.SameComponent a b) :
    P.face.SameCycle a b := by
  let reach : D → Prop := fun d => P.face.SameCycle a d
  have next (d : D) : P.face.SameCycle d (P.face d) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have he (d : D) : P.face.SameCycle d (P.edge d) :=
    face_sameCycle_of_fixed_edge_endpoint P d (h d)
  have hr (d : D) : P.face.SameCycle d (P.rotation d) := by
    have hf : P.face (P.edge (P.rotation d)) = d := by
      apply P.rotation.injective
      rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
      exact P.edge_involutive (P.rotation d)
    have hh := next (P.edge (P.rotation d))
    rw [hf] at hh
    exact ((he (P.rotation d)).trans hh).symm
  have hedge (d : D) : reach (P.edge d) ↔ reach d :=
    ⟨fun hd => hd.trans (he d).symm, fun hd => hd.trans (he d)⟩
  have hrot (d : D) : reach (P.rotation d) ↔ reach d :=
    ⟨fun hd => hd.trans (hr d).symm, fun hd => hd.trans (hr d)⟩
  exact (P.invariant_on_component reach hedge hrot hab).mp (.refl _ _)

/-- Consecutive interior incidences of a star give consecutive
peripheral outlets in its face traversal, with precisely two face steps.
This identifies the cyclic order needed for contiguity intervals. -/
theorem peripheral_face_two_steps {D : Type} (P : RibbonMap D)
    (a b : D) (hb : P.rotation b = b)
    (h : P.rotation (P.edge b) = P.edge a) :
    P.face (P.face a) = b := by
  have hfirst : P.face a = P.edge b := by
    apply P.rotation.injective
    simpa only [RibbonMap.face_apply, Equiv.apply_symm_apply] using h.symm
  rw [hfirst]
  apply P.rotation.injective
  rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
  exact (P.edge_involutive b).trans hb.symm

/-- The one-face statement specialized to compressed coefficient
regions, with no interior-interior edge remaining. -/
theorem coefficient_loopless_component_one_face {D : Type}
    (P : RibbonMap D) (keep : D → Prop)
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hno : ∀ d, keep d → ¬ keep (P.edge d))
    (a b : D) (hab : P.SameComponent a b) :
    P.face.SameCycle a b := by
  classical
  apply face_sameCycle_of_fixed_edge_endpoints P _ a b hab
  intro d
  by_cases hd : keep d
  · exact Or.inr (hleaf _ (hno d hd))
  · exact Or.inl (hleaf d hd)

#print axioms face_sameCycle_of_fixed_edge_endpoint
#print axioms face_sameCycle_of_fixed_edge_endpoints
#print axioms peripheral_face_two_steps
#print axioms coefficient_loopless_component_one_face



/-! ## Separating loops in spherical coefficient ribbons

An interior loop must have distinct incident faces: cutting its endpoint
vertex at the paired darts keeps the component count unchanged, increases
the vertex count, and therefore cannot increase the face count.
This argument also covers loops enclosing other loops or peripheral darts.
-/

/-- Every loop of a spherical ribbon has two distinct incident face cycles. -/
theorem spherical_loop_distinct_faces {D : Type} [Fintype D]
    (P : RibbonMap D) (hE : P.EulerEquality) (a : D)
    (hloop : P.rotation.SameCycle a (P.edge a)) :
    ¬ P.face.SameCycle a (P.edge a) := by
  classical
  let b := P.edge a
  have hne : a ≠ b := (P.edge_ne a).symm
  intro hface
  have next (d : D) : P.face.SameCycle d (P.face d) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have hfa : P.face b = P.rotation.symm a := by
    change P.rotation.symm (P.edge (P.edge a)) = P.rotation.symm a
    rw [P.edge_involutive]
  have hfb : P.face a = P.rotation.symm b := rfl
  have hpred : P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b) := by
    rw [← hfa, ← hfb]
    exact (next b).symm.trans (hface.symm.trans (next a))
  have hv := P.vertexCut_card_vertices_of_sameCycle a b hne hloop
  have he := Fintype.card_congr (P.vertexCutEdgeEquiv a b)
  have hold : P.SameComponent a b := P.component_edge a
  have hnew : (P.vertexCut a b).SameComponent a b :=
    (P.vertexCut a b).component_edge a
  have hc := Fintype.card_congr (P.vertexCutComponentsEquiv a b hold hnew)
  have hf : Fintype.card (P.vertexCut a b).Face = Fintype.card P.Face + 1 := by
    let : Fintype (Cycles P.face) := inferInstanceAs (Fintype P.Face)
    let := Fintype.ofFinite (Cycles (cutAt P.face (P.rotation.symm a) (P.rotation.symm b)))
    have hcast := Fintype.card_congr (Equiv.cast (congrArg Cycles (P.vertexCut_face a b)))
    exact hcast.trans (card_cutAt_of_sameCycle P.face (P.rotation.symm a)
      (P.rotation.symm b) (P.rotation.symm.injective.ne hne) hpred)
  have hu : Fintype.card (P.vertexCut a b).Vertex + Fintype.card (P.vertexCut a b).Face ≤
      Fintype.card (P.vertexCut a b).Edge + 2 * Fintype.card (P.vertexCut a b).Component :=
    (P.vertexCut a b).euler_upper_bound
  change Fintype.card P.Vertex + Fintype.card P.Face =
    Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
  omega

/-- In a compressed spherical coefficient ribbon, the absence of
interior loops is equivalent to every component having a single face
cycle. Thus one cannot discard all internal loops merely from the
star-shape conclusion. -/
theorem coefficient_one_face_iff_no_internal_edges {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hE : P.EulerEquality)
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hterminal : ∀ d, keep d → keep (P.edge d) →
      P.rotation.SameCycle d (P.edge d)) :
    (∀ a b, P.SameComponent a b → P.face.SameCycle a b) ↔
      (∀ d, keep d → ¬ keep (P.edge d)) := by
  constructor
  · intro hone d hd he
    exact spherical_loop_distinct_faces P hE d (hterminal d hd he)
      (hone d (P.edge d) (P.component_edge d))
  · intro hno a b hab
    exact coefficient_loopless_component_one_face P keep hleaf hno a b hab

#print axioms spherical_loop_distinct_faces
#print axioms coefficient_one_face_iff_no_internal_edges



/-! ## Removing an internal loop by a cut and a contraction

This surgery preserves the underlying connectedness and all peripheral
vertex words, but merges the two faces incident to the loop. In particular
it does NOT assert preservation of the separate original face readings,
or that the new interior vertex words vanish in a coefficient quotient.
Those stronger assertions require additional algebraic information.
-/

/-- Cutting at the paired ends of an edge never separates a component:
the edge itself still joins the cut positions. -/
theorem paired_vertexCut_sameComponent {D : Type} (P : RibbonMap D)
    (a d e : D) :
    (P.vertexCut a (P.edge a)).SameComponent d e ↔ P.SameComponent d e := by
  apply P.vertexCut_sameComponent_iff a (P.edge a)
  · exact P.component_edge a
  · exact (P.vertexCut a (P.edge a)).component_edge a

/-- The cut at two interior ends preserves every peripheral vertex
reading and the property that the interior predicate is constant
on rotation cycles. -/
theorem interior_vertexCut_preserves {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (a b : D) (ha : keep a) (hb : keep b) :
    (∀ d e, (P.vertexCut a b).rotation.SameCycle d e → (keep d ↔ keep e)) ∧
      (∀ d, ¬ keep d → (P.vertexCut a b).vertexBoundary d =
        P.vertexBoundary d) := by
  classical
  have hrot (d : D) : keep (P.rotation d) ↔ keep d :=
    (hkeep d (P.rotation d)
      (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))).symm
  have hi := vertexCut_protected_invariant P (fun d => ¬ keep d)
    (fun d => not_congr (hrot d)) a b (fun h => h ha) (fun h => h hb)
  have hnew (d : D) : keep ((P.vertexCut a b).rotation d) ↔ keep d := by
    simpa only [not_not] using not_congr (hi d)
  constructor
  · intro d e h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    clear hn h
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (hnew _).symm
  · intro d hd
    apply vertexCut_other_vertex_read P a b d
    · intro h
      exact hd ((hkeep d a h).mpr ha)
    · intro h
      exact hd ((hkeep d b h).mpr hb)

/-- One genuine internal edge can be removed even if it is a loop.
In the loop case, cut it into a non-loop edge and use the existing
contraction theorem. All assertions concern surviving literal darts. -/
theorem exists_internal_edge_removal {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality) (a : D) (ha : keep a) (hb : keep (P.edge a)) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D),
      Fintype.card E < Fintype.card D ∧
      Q.EulerEquality ∧ (P.Connected → Q.Connected) ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) →
        (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) ∧
      (∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e))) := by
  classical
  have prep : ∃ R : RibbonMap D, R.edge = P.edge ∧
      R.EulerEquality ∧ (P.Connected → R.Connected) ∧
      (∀ d e, R.rotation.SameCycle d e → (keep d ↔ keep e)) ∧
      (∀ d, ¬ keep d → R.vertexBoundary d = P.vertexBoundary d) ∧
      ¬ R.rotation.SameCycle a (R.edge a) := by
    by_cases hl : P.rotation.SameCycle a (P.edge a)
    · let R := P.vertexCut a (P.edge a)
      have hn : a ≠ P.edge a := (P.edge_ne a).symm
      have hcut := interior_vertexCut_preserves P keep hkeep a (P.edge a) ha hb
      refine ⟨R,rfl,P.vertexCut_preserves_euler a (P.edge a) hn hl hE,
        ?_,hcut.1,hcut.2,?_⟩
      · intro hc d e
        exact (paired_vertexCut_sameComponent P a d e).mpr (hc d e)
      · exact SmallPresentationStatements.PermutationCycles.cutAt_not_sameCycle_of_sameCycle
          P.rotation a (P.edge a) hn hl
    · exact ⟨P,rfl,hE,fun h => h,hkeep,fun _ _ => rfl,hl⟩
  obtain ⟨R,he,hR,hconn,hI,hread,hn⟩ := prep
  have hbR : keep (R.edge a) := by rw [he]; exact hb
  let Q := R.contractEdge a
  let f : R.ContractDart a ↪ D := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨R.ContractDart a,inferInstance,Q,f,?_,R.contractEdge_euler a hn hR,
    ?_,?_,?_,?_,?_⟩
  · have hh := R.contractEdge_card_darts a
    omega
  · intro hc
    exact R.contractEdge_connected (hconn hc) a hn
  · intro d
    change (Q.edge d).val = P.edge d.val
    rw [R.contractEdge_edge_val a]
    exact congrFun (congrArg (fun e : Equiv.Perm D => (e : D → D)) he) d.val
  · intro d hd
    exact ⟨⟨d,fun h => hd (h ▸ ha),fun h => hd (h ▸ hbR)⟩,rfl⟩
  · intro d hd
    exact (contractEdge_peripheral_boundary R keep hI a ha hbR d hd).trans
      (hread d.val hd)
  · exact contractEdge_keep_sameVertex R keep hI a ha hbR hn

#print axioms paired_vertexCut_sameComponent
#print axioms interior_vertexCut_preserves
#print axioms exists_internal_edge_removal



/-- Finite iteration of the internal-edge surgery. The terminal
ribbon retains all peripheral darts and their exact vertex readings,
and every remaining edge has a peripheral endpoint. The statement
is purely topological; it does not preserve interior coefficient
relations or the decomposition into original face cycles. -/
theorem exists_internal_edge_free_compression {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D),
      Q.EulerEquality ∧ (P.Connected → Q.Connected) ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) →
        (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) ∧
      (∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e))) ∧
      (∀ d, keep (f d) → ¬ keep (f (Q.edge d))) := by
  classical
  have main : ∀ (n : ℕ) (A : Type) [Fintype A] (R : RibbonMap A)
      (interior : A → Prop), Fintype.card A = n →
      (∀ d e, R.rotation.SameCycle d e → (interior d ↔ interior e)) →
      R.EulerEquality →
      ∃ (B : Type) (_ : Fintype B) (T : RibbonMap B) (j : B ↪ A),
        T.EulerEquality ∧ (R.Connected → T.Connected) ∧
        (∀ d, j (T.edge d) = R.edge (j d)) ∧
        (∀ d, ¬ interior d → ∃ e, j e = d) ∧
        (∀ d, ¬ interior (j d) →
          (T.vertexBoundary d).map j = R.vertexBoundary (j d)) ∧
        (∀ d e, T.rotation.SameCycle d e → (interior (j d) ↔ interior (j e))) ∧
        (∀ d, interior (j d) → ¬ interior (j (T.edge d))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro A inst R interior hcard hinv heuler
      by_cases hex : ∃ a, interior a ∧ interior (R.edge a)
      · obtain ⟨a,ha,ha'⟩ := hex
        obtain ⟨C,instC,U,g,hlt,hU,hconnU,hedgeU,hsurvU,hreadU,hcyclesU⟩ :=
          exists_internal_edge_removal R interior hinv heuler a ha ha'
        let inside : C → Prop := fun d => interior (g d)
        have hn : Fintype.card C < n := by omega
        obtain ⟨B,instB,T,j,hT,hconn,hedge,hsurv,hread,hcycles,hterminal⟩ :=
          ih (Fintype.card C) hn C U inside rfl hcyclesU hU
        let f : B ↪ A := j.trans g
        refine ⟨B,instB,T,f,hT,?_,?_,?_,?_,hcycles,hterminal⟩
        · intro hc
          exact hconn (hconnU hc)
        · intro d
          change g (j (T.edge d)) = R.edge (g (j d))
          rw [hedge,hedgeU]
        · intro d hd
          obtain ⟨c,hc⟩ := hsurvU d hd
          have hci : ¬ inside c := by
            change ¬ interior (g c)
            rw [hc]
            exact hd
          obtain ⟨b,hb⟩ := hsurv c hci
          exact ⟨b,(congrArg g hb).trans hc⟩
        · intro d hd
          change (T.vertexBoundary d).map (fun b => g (j b)) =
            R.vertexBoundary (g (j d))
          calc
            _ = ((T.vertexBoundary d).map j).map g := by
              rw [List.map_map]
              rfl
            _ = (U.vertexBoundary (j d)).map g :=
              congrArg (List.map g) (hread d hd)
            _ = _ := hreadU (j d) hd
      · refine ⟨A,inst,R,Function.Embedding.refl A,heuler,
          fun h => h,fun _ => rfl,?_,?_,hinv,?_⟩
        · intro d _
          exact ⟨d,rfl⟩
        · intro d _
          exact List.map_id _
        · intro d hd hd'
          exact hex ⟨d,hd,hd'⟩
  exact main (Fintype.card D) D P keep rfl hkeep hE

#print axioms exists_internal_edge_free_compression



/-! ## Algebraic invariant for actual interior contractions

Work over an arbitrary group, hence in particular over the quotient by
all lower-rank relators. Contracting distinct interior vertices is valid
with the original labels. Adjacent inverse loops are also harmless.
For a nonadjacent loop the analogous unrestricted statement is false:
the two intervening words can be conjugated relative to one another.
-/

/-- Distinct interior endpoint relations remain true under the
actual edge splice, while the relations at unaffected vertices
remain unchanged. -/
theorem interior_edgeSplice_product_one {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) (hb : keep (P.edge a))
    (hn : ¬ P.rotation.SameCycle a (P.edge a))
    (d : D) (hd : keep d) :
    cycleProduct (P.edgeSplice a).rotation v d = 1 := by
  classical
  have hn' : ¬ P.rotation.SameCycle (P.rotation a) (P.edge a) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  have hra : P.rotation.SameCycle a (P.rotation a) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have hm : cycleProduct (P.edgeSplice a).rotation v (P.rotation a) = 1 := by
    change cycleProduct (cutAt P.rotation (P.rotation a) (P.edge a))
      v (P.rotation a) = 1
    rw [cycleProduct_cutAt_merge P.rotation v _ _ hn',
      hint _ ((hkeep _ _ hra).mp ha), hint _ hb, mul_one]
  by_cases hs : (P.edgeSplice a).rotation.SameCycle (P.rotation a) d
  · exact (cycleProduct_eq_one_of_sameCycle (P.edgeSplice a).rotation v hs).mp hm
  · have hda : ¬ P.rotation.SameCycle d (P.rotation a) := by
      intro h
      exact hs ((P.edgeSplice_sameVertex_iff a hn _ _).mpr (Or.inl h.symm))
    have hdb : ¬ P.rotation.SameCycle d (P.edge a) := by
      intro h
      exact hs ((P.edgeSplice_sameVertex_iff a hn _ _).mpr
        (Or.inr ⟨Or.inl hra.symm,Or.inr h⟩))
    change cycleProduct (cutAt P.rotation (P.rotation a) (P.edge a)) v d = 1
    rw [cycleProduct_cutAt_unchanged P.rotation v _ _ _ hda hdb]
    exact hint d hd

/-- Full algebraic preservation under an actual non-loop interior
edge contraction, including the inverse-label invariant. -/
theorem interior_contractEdge_product_one {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) (hb : keep (P.edge a))
    (hn : ¬ P.rotation.SameCycle a (P.edge a)) :
    (∀ d : P.ContractDart a, v ((P.contractEdge a).edge d).val = (v d.val)⁻¹) ∧
      (∀ d : P.ContractDart a, keep d.val →
        cycleProduct (P.contractEdge a).rotation (fun e => v e.val) d = 1) := by
  constructor
  · intro d
    rw [P.contractEdge_edge_val]
    exact he d.val
  · intro d hd
    let C := P.spliceCancellation a
    have hinv : v C.left * v C.right = 1 := by
      change v a * v (P.edge a) = 1
      rw [he, mul_inv_cancel]
    change (((P.contractEdge a).vertexBoundary d).map (fun e => v e.val)).prod = 1
    rw [show (((P.contractEdge a).vertexBoundary d).map (fun e => v e.val)).prod =
      (((P.edgeSplice a).vertexBoundary d.val).map v).prod from C.vertex_product v hinv d]
    exact interior_edgeSplice_product_one P v keep hkeep hint a ha hb hn d.val hd

/-- In the special case of consecutive inverse incidences, deletion
itself preserves every surviving vertex relation. No commutativity
or restriction to a particular coefficient group is needed. -/
theorem adjacent_internal_product_one {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (C : AdjacentCancellation P)
    (hinv : v C.left * v C.right = 1)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (d : C.Dart) (hd : keep d.val) :
    cycleProduct C.delete.rotation (fun e => v e.val) d = 1 := by
  change ((C.delete.vertexBoundary d).map (fun e => v e.val)).prod = 1
  rw [C.vertex_product v hinv d]
  exact hint d.val hd

/-- The precise group-theoretic correction needed to erase the ends
of a nonconsecutive inverse pair. The two surviving intervals must
retain a conjugation; the naive uncorrected concatenation is not
justified by the old vertex relation. -/
theorem internal_loop_twisted_product {K : Type} [Group K] (x u v : K)
    (h : x * u * x⁻¹ * v = 1) :
    u * (x⁻¹ * v * x) = 1 := by
  calc
    _ = x⁻¹ * (x * u * x⁻¹ * v) * x := by group
    _ = 1 := by rw [h]; simp

#print axioms interior_edgeSplice_product_one
#print axioms interior_contractEdge_product_one
#print axioms adjacent_internal_product_one
#print axioms internal_loop_twisted_product



/-! ## Face potentials: nonabelian change of coefficient coordinates

A face potential acts on the inverse-labelled edges of the dual
ribbon. Products around vertices telescope, so every vertex product
is conjugated, not merely mapped to an unrelated word. Distinct
incident faces allow the label of a loop to be made trivial.
Peripheral singleton labels retain their conjugacy classes, but
need not retain their original values.
-/

/-- The change of coordinates telescopes along every finite walk,
not just along a complete vertex cycle. -/
theorem walk_potential_product {D K : Type} [Group K]
    (sigma : Equiv.Perm D) (v p : D → K)
    {d e : D} {l : List D} (h : Walk sigma d e l) :
    (l.map (fun t => p t * v t * (p (sigma t))⁻¹)).prod =
      p d * (l.map v).prod * (p e)⁻¹ := by
  induction h with
  | nil d => simp
  | cons d e l ht ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [ih]
    group

/-- A potential constant on face cycles induces a change of edge
labels with inverse pairing and conjugated vertex products. -/
theorem face_potential_change {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v g : D → K)
    (hg : ∀ d e, P.face.SameCycle d e → g d = g e)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹) :
    let w := fun d => g (P.edge d) * v d * (g d)⁻¹
    (∀ d, w (P.edge d) = (w d)⁻¹) ∧
      (∀ d, cycleProduct P.rotation w d =
        g (P.edge d) * cycleProduct P.rotation v d * (g (P.edge d))⁻¹) := by
  dsimp only
  constructor
  · intro d
    rw [P.edge_involutive, he]
    group
  · intro d
    have hstep (t : D) : g (P.edge (P.rotation t)) = g t := by
      apply hg
      have hf : P.face (P.edge (P.rotation t)) = t := by
        change P.rotation.symm (P.edge (P.edge (P.rotation t))) = t
        rw [P.edge_involutive, Equiv.symm_apply_apply]
      have hs : P.face.SameCycle (P.edge (P.rotation t))
          (P.face (P.edge (P.rotation t))) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      rwa [hf] at hs
    have hw := walk_potential_product P.rotation v (fun t => g (P.edge t))
      (cycleBoundary_walk P.rotation d)
    change ((cycleBoundary P.rotation d).map
      (fun t => g (P.edge t) * v t * (g (P.edge (P.rotation t)))⁻¹)).prod =
      g (P.edge d) * ((cycleBoundary P.rotation d).map v).prod *
        (g (P.edge d))⁻¹ at hw
    simpa only [hstep,cycleProduct] using hw

/-- A spherical loop can be normalized to label one on both of its
incidences by changing only group coordinates. Every vertex product
is conjugated and every edge remains inverse-labelled. -/
theorem spherical_loop_normalize_label {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hE : P.EulerEquality) (a : D)
    (hloop : P.rotation.SameCycle a (P.edge a)) :
    ∃ w g : D → K, w a = 1 ∧ w (P.edge a) = 1 ∧
      (∀ d, w (P.edge d) = (w d)⁻¹) ∧
      (∀ d, cycleProduct P.rotation w d =
        g (P.edge d) * cycleProduct P.rotation v d * (g (P.edge d))⁻¹) := by
  classical
  have hn := spherical_loop_distinct_faces P hE a hloop
  let g : D → K := fun d => if P.face.SameCycle a d then v a else 1
  let w : D → K := fun d => g (P.edge d) * v d * (g d)⁻¹
  have hg (d e : D) (h : P.face.SameCycle d e) : g d = g e := by
    have hi : P.face.SameCycle a d ↔ P.face.SameCycle a e :=
      ⟨fun hd => hd.trans h,fun he' => he'.trans h.symm⟩
    simp only [g,hi]
  have hp := face_potential_change P v g hg he
  have hga : g a = v a  := ite_eq_left (.refl _ _)
  have hgb : g (P.edge a) = 1 := ite_eq_right hn
  have hwa : w a = 1 := by
    change g (P.edge a) * v a * (g a)⁻¹ = 1
    rw [hga,hgb,one_mul,mul_inv_cancel]
  refine ⟨w,g,hwa,?_,hp.1,hp.2⟩
  rw [show w (P.edge a) = (w a)⁻¹ from hp.1 a,hwa,inv_one]

/-- Conjugating all vertex products preserves all prescribed
identity relations, independently of the choice of protected vertices. -/
theorem conjugated_vertex_relations {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v w g : D → K) (keep : D → Prop)
    (h : ∀ d, cycleProduct P.rotation w d =
      g d * cycleProduct P.rotation v d * (g d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1) :
    ∀ d, keep d → cycleProduct P.rotation w d = 1 := by
  intro d hd
  rw [h,hint d hd,mul_one,mul_inv_cancel]

#print axioms walk_potential_product
#print axioms face_potential_change
#print axioms spherical_loop_normalize_label
#print axioms conjugated_vertex_relations



/-! ## Algebraically sound removal of a normalized internal loop

The cut splits one vertex product into two factors, not necessarily
individual relations. Splicing them back after normalizing the loop
label preserves their product. Only then delete the consecutive pair.
-/

/-- Advancing the based vertex reading by one incidence of value one
leaves the product literally unchanged. -/
theorem cycleProduct_next_of_one {D K : Type} [Finite D] [Group K]
    (sigma : Equiv.Perm D) (v : D → K) (a : D) (ha : v a = 1) :
    cycleProduct sigma v (sigma a) = cycleProduct sigma v a := by
  obtain ⟨l,hl⟩ := cycleBoundary_cons sigma a
  simp only [cycleProduct,cycleBoundary_next sigma a l hl,hl,
    List.map_append,List.map_cons,List.map_nil,List.prod_append,
    List.prod_cons,List.prod_nil,ha,one_mul,mul_one]

/-- Cut a loop into two vertices and splice it back. If its label has
been made trivial, the merged vertex is still a relation. Other
vertices retain their original products. -/
theorem normalized_loop_splice_product_one {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) (hloop : P.rotation.SameCycle a (P.edge a))
    (hv : v a = 1) :
    let R := P.vertexCut a (P.edge a)
    ∀ d, keep d → cycleProduct (R.edgeSplice a).rotation v d = 1 := by
  classical
  intro R d hd
  let b := P.edge a
  have hn : ¬ R.rotation.SameCycle a b :=
    cutAt_not_sameCycle_of_sameCycle P.rotation a b (P.edge_ne a).symm hloop
  have hn' : ¬ R.rotation.SameCycle (R.rotation a) b := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  let S := R.edgeSplice a
  have hpart : cycleProduct P.rotation v a =
      cycleProduct R.rotation v a * cycleProduct R.rotation v b := by
    change ((P.vertexBoundary a).map v).prod =
      ((R.vertexBoundary a).map v).prod * ((R.vertexBoundary b).map v).prod
    rw [vertexCut_partition P a b (P.edge_ne a).symm hloop,
      List.map_append,List.prod_append]
  have hmerge : cycleProduct S.rotation v (R.rotation a) = 1 := by
    change cycleProduct (cutAt R.rotation (R.rotation a) b) v (R.rotation a) = 1
    rw [cycleProduct_cutAt_merge R.rotation v _ _ hn',
      cycleProduct_next_of_one R.rotation v a hv,← hpart]
    exact hint a ha
  have hra : R.rotation.SameCycle a (R.rotation a) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  by_cases hs : S.rotation.SameCycle (R.rotation a) d
  · exact (cycleProduct_eq_one_of_sameCycle S.rotation v hs).mp hmerge
  · have hda : ¬ R.rotation.SameCycle d (R.rotation a) := by
      intro h
      exact hs ((R.edgeSplice_sameVertex_iff a hn _ _).mpr (Or.inl h.symm))
    have hdb : ¬ R.rotation.SameCycle d b := by
      intro h
      exact hs ((R.edgeSplice_sameVertex_iff a hn _ _).mpr
        (Or.inr ⟨Or.inl hra.symm,Or.inr h⟩))
    have hdaOld : ¬ P.rotation.SameCycle a d := by
      intro h
      have hm := (P.mem_vertexBoundary_iff a d).mpr h
      rw [vertexCut_partition P a b (P.edge_ne a).symm hloop,List.mem_append] at hm
      rcases hm with hm | hm
      · exact hda (((R.mem_vertexBoundary_iff a d).mp hm).symm.trans hra)
      · exact hdb ((R.mem_vertexBoundary_iff b d).mp hm).symm
    have hread : R.vertexBoundary d = P.vertexBoundary d :=
      vertexCut_other_vertex_read P a b d (fun h => hdaOld h.symm)
        (fun h => hdaOld (hloop.trans h.symm))
    change cycleProduct (cutAt R.rotation (R.rotation a) b) v d = 1
    rw [cycleProduct_cutAt_unchanged R.rotation v _ _ _ hda hdb]
    change ((R.vertexBoundary d).map v).prod = 1
    rw [hread]
    exact hint d hd

/-- The actual loop removal preserves all interior identity products
after the face-coordinate normalization. The remaining labels are
inverse along the original surviving edge pairs. -/
theorem normalized_loop_removal_product_one {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) (hloop : P.rotation.SameCycle a (P.edge a))
    (hv : v a = 1) :
    let R := P.vertexCut a (P.edge a)
    (∀ d : R.ContractDart a, v ((R.contractEdge a).edge d).val = (v d.val)⁻¹) ∧
      (∀ d : R.ContractDart a, keep d.val →
        cycleProduct (R.contractEdge a).rotation (fun e => v e.val) d = 1) := by
  intro R
  constructor
  · intro d
    rw [R.contractEdge_edge_val]
    exact he d.val
  · intro d hd
    let C := R.spliceCancellation a
    have hinv : v C.left * v C.right = 1 := by
      change v a * v (P.edge a) = 1
      rw [he,mul_inv_cancel]
    change (((R.contractEdge a).vertexBoundary d).map (fun e => v e.val)).prod = 1
    rw [show (((R.contractEdge a).vertexBoundary d).map (fun e => v e.val)).prod =
      (((R.edgeSplice a).vertexBoundary d.val).map v).prod from C.vertex_product v hinv d]
    exact normalized_loop_splice_product_one P v keep hint a ha hloop hv d.val hd

#print axioms cycleProduct_next_of_one
#print axioms normalized_loop_splice_product_one
#print axioms normalized_loop_removal_product_one



/-! ## Algebraic compression with peripheral conjugacy certificates

The literal embedding of surviving darts is tracked independently of
their changed coefficient values. Peripheral cycle products are
preserved up to conjugacy, not necessarily literally. This distinction
is essential before any quantitative application.
-/

/-- Transporting a complete based dart list transports its product. -/
theorem cycleProduct_of_boundary_map {D E K : Type} [Finite D] [Finite E] [Group K]
    (P : RibbonMap D) (Q : RibbonMap E) (f : E → D) (v : D → K) (d : E)
    (h : (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) :
    cycleProduct Q.rotation (fun e => v (f e)) d =
      cycleProduct P.rotation v (f d) := by
  change ((Q.vertexBoundary d).map (fun e => v (f e))).prod =
    ((P.vertexBoundary (f d)).map v).prod
  rw [← h,List.map_map]
  rfl

/-- Delete one internal edge with all interior products still equal to
one and an explicit conjugacy certificate at each peripheral vertex. -/
theorem exists_algebraic_internal_edge_removal {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) (hb : keep (P.edge a)) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D) (w : E → K),
      Fintype.card E < Fintype.card D ∧ Q.EulerEquality ∧
      (P.Connected → Q.Connected) ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) → (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) ∧
      (∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e))) ∧
      (∀ d, w (Q.edge d) = (w d)⁻¹) ∧
      (∀ d, keep (f d) → cycleProduct Q.rotation w d = 1) ∧
      (∀ d, ¬ keep (f d) → ∃ g : K,
        cycleProduct Q.rotation w d = g * cycleProduct P.rotation v (f d) * g⁻¹) := by
  classical
  have prep : ∃ (R : RibbonMap D) (z : D → K), R.edge = P.edge ∧
      R.EulerEquality ∧ (P.Connected → R.Connected) ∧
      (∀ d e, R.rotation.SameCycle d e → (keep d ↔ keep e)) ∧
      (∀ d, ¬ keep d → R.vertexBoundary d = P.vertexBoundary d) ∧
      ¬ R.rotation.SameCycle a (R.edge a) ∧
      (∀ d : R.ContractDart a, z ((R.contractEdge a).edge d).val = (z d.val)⁻¹) ∧
      (∀ d : R.ContractDart a, keep d.val →
        cycleProduct (R.contractEdge a).rotation (fun e => z e.val) d = 1) ∧
      (∀ d, ∃ g : K, cycleProduct P.rotation z d = g * cycleProduct P.rotation v d * g⁻¹) := by
    by_cases hl : P.rotation.SameCycle a (P.edge a)
    · let R := P.vertexCut a (P.edge a)
      have hn : a ≠ P.edge a := (P.edge_ne a).symm
      obtain ⟨z,g,hza,_,hze,hzg⟩ := spherical_loop_normalize_label P v he hE a hl
      have hi := conjugated_vertex_relations P v z (fun d => g (P.edge d)) keep hzg hint
      have hcut := interior_vertexCut_preserves P keep hkeep a (P.edge a) ha hb
      have hp := normalized_loop_removal_product_one P z keep hze hi a ha hl hza
      refine ⟨R,z,rfl,P.vertexCut_preserves_euler a (P.edge a) hn hl hE,
        ?_,hcut.1,hcut.2,?_,hp.1,hp.2,?_⟩
      · intro hc d e
        exact (paired_vertexCut_sameComponent P a d e).mpr (hc d e)
      · exact cutAt_not_sameCycle_of_sameCycle P.rotation a (P.edge a) hn hl
      · intro d
        exact ⟨g (P.edge d),hzg d⟩
    · have hp := interior_contractEdge_product_one P v keep hkeep he hint a ha hb hl
      refine ⟨P,v,rfl,hE,fun h => h,hkeep,fun _ _ => rfl,hl,hp.1,hp.2,?_⟩
      intro d
      exact ⟨1,by simp⟩
  obtain ⟨R,z,heR,hR,hconn,hI,hread,hn,hzinv,hzone,hzg⟩ := prep
  have hbR : keep (R.edge a) := by rw [heR]; exact hb
  let Q := R.contractEdge a
  let f : R.ContractDart a ↪ D := ⟨Subtype.val,Subtype.val_injective⟩
  have hboundary (d : R.ContractDart a) (hd : ¬ keep d.val) :
      (Q.vertexBoundary d).map Subtype.val = P.vertexBoundary d.val :=
    (contractEdge_peripheral_boundary R keep hI a ha hbR d hd).trans (hread d.val hd)
  refine ⟨R.ContractDart a,inferInstance,Q,f,fun d => z d.val,?_,
    R.contractEdge_euler a hn hR,?_,?_,?_,hboundary,
    contractEdge_keep_sameVertex R keep hI a ha hbR hn,hzinv,hzone,?_⟩
  · have hh := R.contractEdge_card_darts a
    omega
  · intro hc
    exact R.contractEdge_connected (hconn hc) a hn
  · intro d
    change (Q.edge d).val = P.edge d.val
    rw [R.contractEdge_edge_val a]
    exact congrFun (congrArg (fun e : Equiv.Perm D => (e : D → D)) heR) d.val
  · intro d hd
    exact ⟨⟨d,fun h => hd (h ▸ ha),fun h => hd (h ▸ hbR)⟩,rfl⟩
  · intro d hd
    obtain ⟨g,hg⟩ := hzg d.val
    refine ⟨g,?_⟩
    exact (cycleProduct_of_boundary_map P Q Subtype.val z d (hboundary d hd)).trans hg

/-- Terminate the algebraic surgery by strict induction on the number
of darts. The result is an interior-edge-free spherical ribbon, with
all interior relations valid and each old peripheral product retained
up to an individual conjugation. -/
theorem exists_algebraic_internal_edge_free_compression {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1) :
    ∃ (E : Type) (_ : Fintype E) (Q : RibbonMap E) (f : E ↪ D) (w : E → K),
      Q.EulerEquality ∧ (P.Connected → Q.Connected) ∧
      (∀ d, f (Q.edge d) = P.edge (f d)) ∧
      (∀ d, ¬ keep d → ∃ e, f e = d) ∧
      (∀ d, ¬ keep (f d) → (Q.vertexBoundary d).map f = P.vertexBoundary (f d)) ∧
      (∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e))) ∧
      (∀ d, keep (f d) → ¬ keep (f (Q.edge d))) ∧
      (∀ d, w (Q.edge d) = (w d)⁻¹) ∧
      (∀ d, keep (f d) → cycleProduct Q.rotation w d = 1) ∧
      (∀ d, ¬ keep (f d) → ∃ g : K,
        cycleProduct Q.rotation w d = g * cycleProduct P.rotation v (f d) * g⁻¹) := by
  classical
  have main : ∀ (n : ℕ) (A : Type) [Fintype A] (R : RibbonMap A)
      (z : A → K) (interior : A → Prop), Fintype.card A = n →
      (∀ d e, R.rotation.SameCycle d e → (interior d ↔ interior e)) →
      R.EulerEquality → (∀ d, z (R.edge d) = (z d)⁻¹) →
      (∀ d, interior d → cycleProduct R.rotation z d = 1) →
      ∃ (B : Type) (_ : Fintype B) (T : RibbonMap B) (j : B ↪ A) (u : B → K),
        T.EulerEquality ∧ (R.Connected → T.Connected) ∧
        (∀ d, j (T.edge d) = R.edge (j d)) ∧
        (∀ d, ¬ interior d → ∃ e, j e = d) ∧
        (∀ d, ¬ interior (j d) → (T.vertexBoundary d).map j = R.vertexBoundary (j d)) ∧
        (∀ d e, T.rotation.SameCycle d e → (interior (j d) ↔ interior (j e))) ∧
        (∀ d, interior (j d) → ¬ interior (j (T.edge d))) ∧
        (∀ d, u (T.edge d) = (u d)⁻¹) ∧
        (∀ d, interior (j d) → cycleProduct T.rotation u d = 1) ∧
        (∀ d, ¬ interior (j d) → ∃ g : K,
          cycleProduct T.rotation u d = g * cycleProduct R.rotation z (j d) * g⁻¹) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro A inst R z interior hcard hinv hEuler hz hrel
      by_cases hex : ∃ a, interior a ∧ interior (R.edge a)
      · obtain ⟨a,ha,hb⟩ := hex
        obtain ⟨C,instC,U,k,y,hlt,hU,hconnU,hedgeU,hsurvU,hreadU,hcyclesU,hy,hrelU,hconjU⟩ :=
          exists_algebraic_internal_edge_removal R z interior hinv hEuler hz hrel a ha hb
        let inside : C → Prop := fun d => interior (k d)
        have hn : Fintype.card C < n := by omega
        obtain ⟨B,instB,T,j,u,hT,hconn,hedge,hsurv,hread,hcycles,hterminal,hu,hrelT,hconj⟩ :=
          ih (Fintype.card C) hn C U y inside rfl hcyclesU hU hy hrelU
        let f : B ↪ A := j.trans k
        refine ⟨B,instB,T,f,u,hT,?_,?_,?_,?_,hcycles,hterminal,hu,hrelT,?_⟩
        · intro hc
          exact hconn (hconnU hc)
        · intro d
          change k (j (T.edge d)) = R.edge (k (j d))
          rw [hedge,hedgeU]
        · intro d hd
          obtain ⟨c,hc⟩ := hsurvU d hd
          have hci : ¬ inside c := by
            change ¬ interior (k c)
            rw [hc]
            exact hd
          obtain ⟨b,hb'⟩ := hsurv c hci
          exact ⟨b,(congrArg k hb').trans hc⟩
        · intro d hd
          change (T.vertexBoundary d).map (fun b => k (j b)) = R.vertexBoundary (k (j d))
          calc
            _ = ((T.vertexBoundary d).map j).map k := by rw [List.map_map]; rfl
            _ = (U.vertexBoundary (j d)).map k := congrArg (List.map k) (hread d hd)
            _ = _ := hreadU (j d) hd
        · intro d hd
          obtain ⟨g,hg⟩ := hconj d hd
          obtain ⟨l,hl⟩ := hconjU (j d) hd
          refine ⟨g*l,?_⟩
          change cycleProduct T.rotation u d =
            (g*l) * cycleProduct R.rotation z (k (j d)) * (g*l)⁻¹
          rw [hg,hl]
          group
      · refine ⟨A,inst,R,Function.Embedding.refl A,z,hEuler,
          fun h => h,fun _ => rfl,?_,?_,hinv,?_,hz,hrel,?_⟩
        · intro d _
          exact ⟨d,rfl⟩
        · intro d _
          exact List.map_id _
        · intro d hd hd'
          exact hex ⟨d,hd,hd'⟩
        · intro d _
          exact ⟨1,by simp⟩
  exact main (Fintype.card D) D P v keep rfl hkeep hE he hint

#print axioms cycleProduct_of_boundary_map
#print axioms exists_algebraic_internal_edge_removal
#print axioms exists_algebraic_internal_edge_free_compression



/-! ## Protected peripheral labels and invariant quantitative data

A singleton peripheral vertex lies on the same face cycle on both
sides of its incident edge. Thus face potentials conjugate its
label. A potential can be chosen to leave any one prescribed face
unchanged, while normalizing a chosen internal loop.
-/

/-- A fixed rotation point has its label changed only by conjugation. -/
theorem face_potential_fixed_vertex_label {D K : Type} [Group K]
    (P : RibbonMap D) (v g : D → K)
    (hg : ∀ d e, P.face.SameCycle d e → g d = g e)
    (d : D) (hd : P.rotation d = d) :
    g (P.edge d) * v d * (g d)⁻¹ = g d * v d * (g d)⁻¹ := by
  rw [hg _ _ (face_sameCycle_of_fixed_edge_endpoint P d (Or.inl hd)).symm]

/-- The normalization can fix a designated face, even when that
face is incident to the loop. The protected face need not be an
outside face of the original ribbon. -/
theorem spherical_loop_normalize_protected_face {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hE : P.EulerEquality) (a o : D)
    (hl : P.rotation.SameCycle a (P.edge a)) :
    ∃ w g : D → K,
      (∀ d, P.face.SameCycle o d → g d = 1) ∧
      (∀ d, P.face.SameCycle o d → P.face.SameCycle o (P.edge d) → w d = v d) ∧
      w a = 1 ∧ w (P.edge a) = 1 ∧
      (∀ d, w (P.edge d) = (w d)⁻¹) ∧
      (∀ d, cycleProduct P.rotation w d =
        g (P.edge d) * cycleProduct P.rotation v d * (g (P.edge d))⁻¹) := by
  classical
  have hn := spherical_loop_distinct_faces P hE a hl
  let g : D → K := if P.face.SameCycle o a then
      fun d => if P.face.SameCycle (P.edge a) d then (v a)⁻¹ else 1
    else fun d => if P.face.SameCycle a d then v a else 1
  let w : D → K := fun d => g (P.edge d) * v d * (g d)⁻¹
  have hg (d e : D) (h : P.face.SameCycle d e) : g d = g e := by
    have hi (t : D) : P.face.SameCycle t d ↔ P.face.SameCycle t e :=
      ⟨fun hd => hd.trans h,fun he' => he'.trans h.symm⟩
    by_cases hoa : P.face.SameCycle o a
    · simp only [g,ite_eq_left hoa,hi (P.edge a)]
    · simp only [g,ite_eq_right hoa,hi a]
  have hprotect (d : D) (hd : P.face.SameCycle o d) : g d = 1 := by
    by_cases hoa : P.face.SameCycle o a
    · have hno : ¬ P.face.SameCycle (P.edge a) d := by
        intro h
        exact hn (hoa.symm.trans (hd.trans h.symm))
      simp only [g,ite_eq_left hoa,ite_eq_right hno]
    · have hno : ¬ P.face.SameCycle a d := fun h => hoa (hd.trans h.symm)
      simp only [g,ite_eq_right hoa,ite_eq_right hno]
  have hp := face_potential_change P v g hg he
  have hwa : w a = 1 := by
    change g (P.edge a) * v a * (g a)⁻¹ = 1
    by_cases hoa : P.face.SameCycle o a
    · have hna : ¬ P.face.SameCycle (P.edge a) a := fun h => hn h.symm
      have hself : P.face.SameCycle (P.edge a) (P.edge a) := .refl _ _
      simp only [g,ite_eq_left hoa,ite_eq_left hself,ite_eq_right hna,
        inv_mul_cancel,inv_one,one_mul]
    · have hself : P.face.SameCycle a a := .refl _ _
      simp only [g,ite_eq_right hoa,ite_eq_left hself,ite_eq_right hn,
        one_mul,mul_inv_cancel]
  refine ⟨w,g,hprotect,?_,hwa,?_,hp.1,hp.2⟩
  · intro d hd he'
    change g (P.edge d) * v d * (g d)⁻¹ = v d
    rw [hprotect _ hd,hprotect _ he',inv_one,one_mul,mul_one]
  · rw [show w (P.edge a) = (w a)⁻¹ from hp.1 a,hwa,inv_one]

/-- A singleton incident to the protected face keeps its exact
coefficient value under the protected normalization. -/
theorem protected_face_singleton_value {D K : Type} [Group K]
    (P : RibbonMap D) (v w : D → K) (o d : D)
    (h : ∀ e, P.face.SameCycle o e → P.face.SameCycle o (P.edge e) → w e = v e)
    (hd : P.rotation d = d) (ho : P.face.SameCycle o d) : w d = v d :=
  h d ho (ho.trans (face_sameCycle_of_fixed_edge_endpoint P d (Or.inl hd)))

/-- Every conjugacy-invariant numerical weight is preserved exactly
by the peripheral product certificates, including the indicator of
a nontrivial coefficient. No claim is made for arbitrary raw length. -/
theorem peripheral_conjugacy_weight {D E K : Type} [Finite D] [Finite E] [Group K]
    (P : RibbonMap D) (Q : RibbonMap E) (f : E → D)
    (v : D → K) (w : E → K) (keep : D → Prop) (weight : K → ℕ)
    (hw : ∀ g x, weight (g*x*g⁻¹) = weight x)
    (hc : ∀ d, ¬ keep (f d) → ∃ g : K,
      cycleProduct Q.rotation w d = g * cycleProduct P.rotation v (f d) * g⁻¹)
    (d : E) (hd : ¬ keep (f d)) :
    weight (cycleProduct Q.rotation w d) = weight (cycleProduct P.rotation v (f d)) := by
  obtain ⟨g,hg⟩ := hc d hd
  rw [hg,hw]

#print axioms face_potential_fixed_vertex_label
#print axioms spherical_loop_normalize_protected_face
#print axioms protected_face_singleton_value
#print axioms peripheral_conjugacy_weight



/-! ## Peripheral enumeration after algebraic compression

The surviving peripheral darts form an exact finite copy of the
original peripheral darts. Hence all original combinatorial weights
can be counted without using the new spelling of group elements.
-/

/-- The surviving peripheral dart embedding is a bijection onto the
original peripheral dart type. -/
noncomputable def compressed_peripheral_equiv {D E : Type}
    (f : E ↪ D) (keep : D → Prop)
    (hsurv : ∀ d, ¬ keep d → ∃ e, f e = d) :
    {e : E // ¬ keep (f e)} ≃ {d : D // ¬ keep d} :=
  Equiv.ofBijective (fun e => ⟨f e.val,e.property⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h)
    · intro d
      obtain ⟨e,he⟩ := hsurv d.val d.property
      have hp : ¬ keep (f e) := by rw [he]; exact d.property
      exact ⟨⟨e,hp⟩,Subtype.ext he⟩)

/-- The number of peripheral incidences is exactly preserved. -/
theorem compressed_peripheral_card {D E : Type}
    [Fintype D] [Fintype E] (f : E ↪ D) (keep : D → Prop)
    [DecidablePred keep] [DecidablePred (fun e => keep (f e))]
    (hsurv : ∀ d, ¬ keep d → ∃ e, f e = d) :
    Fintype.card {e : E // ¬ keep (f e)} =
      Fintype.card {d : D // ¬ keep d} :=
  Fintype.card_congr (compressed_peripheral_equiv f keep hsurv)

/-- The exact sum of arbitrary original peripheral dart weights is
preserved by the canonical bijection. This concerns original
combinatorial weights, not lengths of newly conjugated labels. -/
theorem compressed_peripheral_weight_sum {D E : Type}
    [Fintype D] [Fintype E] (f : E ↪ D) (keep : D → Prop)
    [DecidablePred keep] [DecidablePred (fun e => keep (f e))]
    (hsurv : ∀ d, ¬ keep d → ∃ e, f e = d) (weight : D → ℕ) :
    (∑ e : {e : E // ¬ keep (f e)}, weight (f e.val)) =
      ∑ d : {d : D // ¬ keep d}, weight d.val := by
  apply Fintype.sum_equiv (compressed_peripheral_equiv f keep hsurv)
  intro e
  rfl

/-- Conjugacy certificates also preserve the distinction between
trivial and nontrivial peripheral products. -/
theorem compressed_peripheral_nontrivial_iff {D E K : Type}
    [Finite D] [Finite E] [Group K]
    (P : RibbonMap D) (Q : RibbonMap E) (f : E → D)
    (v : D → K) (w : E → K) (keep : D → Prop)
    (hc : ∀ d, ¬ keep (f d) → ∃ g : K,
      cycleProduct Q.rotation w d = g * cycleProduct P.rotation v (f d) * g⁻¹)
    (d : E) (hd : ¬ keep (f d)) :
    cycleProduct Q.rotation w d ≠ 1 ↔ cycleProduct P.rotation v (f d) ≠ 1 := by
  obtain ⟨g,hg⟩ := hc d hd
  rw [hg]
  constructor
  · intro h hn
    apply h
    rw [hn,mul_one,mul_inv_cancel]
  · intro h hn
    apply h
    calc
      cycleProduct P.rotation v (f d) =
        g⁻¹ * (g * cycleProduct P.rotation v (f d) * g⁻¹) * g := by group
      _ = 1 := by rw [hn]; simp

#print axioms compressed_peripheral_equiv
#print axioms compressed_peripheral_card
#print axioms compressed_peripheral_weight_sum
#print axioms compressed_peripheral_nontrivial_iff



/-! ## Exact enumeration of the outlets of a loop-free star

The central cycle determines a genuine ordered list of peripheral
outlets. It enumerates each outlet exactly once and the inverse
coefficient product is one. This is a local region equation, not
yet a family of contiguity bands between original relator cells.
-/

/-- The ordered edge mates of the central cycle are precisely the
peripheral darts of its component, without repetitions. -/
theorem loopless_star_outlet_list {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hno : ∀ d, keep d → ¬ keep (P.edge d))
    (a : D) (ha : keep a) :
    ((P.vertexBoundary a).map P.edge).Nodup ∧
      (∀ b, b ∈ (P.vertexBoundary a).map P.edge ↔
        P.SameComponent a b ∧ ¬ keep b) := by
  constructor
  · exact (cycleBoundary_nodup P.rotation a).map P.edge.injective
  · intro b
    constructor
    · intro hm
      obtain ⟨d,hd,hdb⟩ := List.mem_map.mp hm
      have hc := (P.mem_vertexBoundary_iff a d).mp hd
      have hkd := (hkeep a d hc).mp ha
      refine ⟨?_,?_⟩
      · rw [← hdb]
        exact Relation.EqvGen.trans _ _ _ (P.component_of_vertexCycle hc)
          (P.component_edge d)
      · rw [← hdb]
        exact hno d hkd
    · rintro ⟨hc,hb⟩
      have hterminal : ∀ d, keep d → keep (P.edge d) →
          P.rotation.SameCycle d (P.edge d) :=
        fun d hd he => (hno d hd he).elim
      have h := (compressed_region_star P keep hkeep hleaf hterminal a ha b hc).2 hb
      exact List.mem_map.mpr ⟨P.edge b,(P.mem_vertexBoundary_iff a _).mpr h,
        P.edge_involutive b⟩

/-- The ordered outlet list carries a genuine nonabelian equation
using inverse labels. No order-independent product is asserted. -/
theorem loopless_star_outlet_product {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hno : ∀ d, keep d → ¬ keep (P.edge d))
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (a : D) (ha : keep a) :
    ∃ l : List D, l.Nodup ∧
      (∀ b, b ∈ l ↔ P.SameComponent a b ∧ ¬ keep b) ∧
      (l.map (fun b => (v b)⁻¹)).prod = 1 := by
  have hl := loopless_star_outlet_list P keep hkeep hleaf hno a ha
  refine ⟨(P.vertexBoundary a).map P.edge,hl.1,hl.2,?_⟩
  rw [List.map_map]
  change ((P.vertexBoundary a).map (fun d => (v (P.edge d))⁻¹)).prod = 1
  simp only [he,inv_inv]
  exact hint a ha

/-- At a peripheral singleton, the based product is its actual label. -/
theorem peripheral_singleton_product {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K) (d : D) (hd : P.rotation d = d) :
    cycleProduct P.rotation v d = v d := by
  change ((P.vertexBoundary d).map v).prod = v d
  rw [fixed_vertex_read_singleton P d hd]
  simp

/-- For an algebraically compressed star, every outlet contributes
an individually conjugated original value. Its ordered inverse
product is a relation in the coefficient group. -/
theorem loopless_star_original_outlet_equation {D E K : Type}
    [Fintype D] [Fintype E] [Group K]
    (P : RibbonMap D) (Q : RibbonMap E) (f : E ↪ D)
    (v : D → K) (w : E → K) (keep : D → Prop)
    (hkeep : ∀ d e, Q.rotation.SameCycle d e → (keep (f d) ↔ keep (f e)))
    (hleaf : ∀ d, ¬ keep (f d) → Q.rotation d = d)
    (hno : ∀ d, keep (f d) → ¬ keep (f (Q.edge d)))
    (he : ∀ d, w (Q.edge d) = (w d)⁻¹)
    (hint : ∀ d, keep (f d) → cycleProduct Q.rotation w d = 1)
    (hc : ∀ d, ¬ keep (f d) → ∃ g : K,
      cycleProduct Q.rotation w d = g * cycleProduct P.rotation v (f d) * g⁻¹)
    (a : E) (ha : keep (f a)) :
    ∃ (l : List E) (g : E → K), l.Nodup ∧
      (∀ b, b ∈ l ↔ Q.SameComponent a b ∧ ¬ keep (f b)) ∧
      (l.map (fun b => (g b * cycleProduct P.rotation v (f b) * (g b)⁻¹)⁻¹)).prod = 1 := by
  classical
  obtain ⟨l,hnd,hm,hprod⟩ := loopless_star_outlet_product Q w
    (fun d => keep (f d)) hkeep hleaf hno he hint a ha
  have hc' : ∀ b, ∃ g : K, ¬ keep (f b) →
      w b = g * cycleProduct P.rotation v (f b) * g⁻¹ := by
    intro b
    by_cases hb : keep (f b)
    · exact ⟨1,fun hn => (hn hb).elim⟩
    · obtain ⟨g,hg⟩ := hc b hb
      refine ⟨g,fun _ => ?_⟩
      rw [peripheral_singleton_product Q w b (hleaf b hb)] at hg
      exact hg
  choose g hg using hc'
  refine ⟨l,g,hnd,hm,?_⟩
  have hl : l.map (fun b => (g b * cycleProduct P.rotation v (f b) * (g b)⁻¹)⁻¹) =
      l.map (fun b => (w b)⁻¹) := by
    apply List.map_congr_left
    intro b hb
    rw [← hg b ((hm b).mp hb).2]
  rw [hl]
  exact hprod

#print axioms loopless_star_outlet_list
#print axioms loopless_star_outlet_product
#print axioms peripheral_singleton_product
#print axioms loopless_star_original_outlet_equation



/-! ## Connected coefficient region: an ordered relation on every outlet

Apply the compression separately to a connected component. This
avoids any implicit assumption that a global compression preserves
the original component partition. The isolated-edge case is handled
explicitly, as well as the star case.
-/

/-- Every connected spherical coefficient region with singleton
peripheral vertices admits a list enumerating all its original
outlets, whose suitably conjugated inverse labels multiply to one.
The list and the conjugators are obtained from actual surgery. -/
theorem connected_coefficient_outlet_equation {D K : Type}
    [Fintype D] [Group K] (P : RibbonMap D) (v : D → K)
    (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hE : P.EulerEquality) (hconn : P.Connected)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (o : D) (ho : ¬ keep o) :
    ∃ (l : List D) (g : D → K),
      l.Nodup ∧ (∀ d, d ∈ l ↔ ¬ keep d) ∧
      (l.map (fun d => (g d * v d * (g d)⁻¹)⁻¹)).prod = 1 := by
  classical
  obtain ⟨E,inst,Q,f,w,hQ,hconnQ,_,hsurv,hread,hcycles,hno,hw,hrel,hconj⟩ :=
    exists_algebraic_internal_edge_free_compression P v keep hkeep hE he hint
  have hleafQ : ∀ d, ¬ keep (f d) → Q.rotation d = d :=
    compressed_peripheral_leaf P Q f keep hread hleaf
  obtain ⟨a,ha⟩ := hsurv o ho
  have hka : ¬ keep (f a) := by rw [ha]; exact ho
  have hco := hconnQ hconn
  have hlocal : ∃ l : List E, l.Nodup ∧
      (∀ b, b ∈ l ↔ ¬ keep (f b)) ∧
      (l.map (fun b => (w b)⁻¹)).prod = 1 := by
    by_cases h : keep (f (Q.edge a))
    · obtain ⟨l,hnd,hm,hprod⟩ := loopless_star_outlet_product Q w
        (fun d => keep (f d)) hcycles hleafQ hno hw hrel (Q.edge a) h
      exact ⟨l,hnd,fun b => (hm b).trans (and_iff_right (hco _ _)),hprod⟩
    · refine ⟨[a,Q.edge a],?_,?_,?_⟩
      · simp [Ne.symm (Q.edge_ne a)]
      · intro b
        have hh := peripheral_edge_component Q a b (hleafQ a hka)
          (hleafQ _ h)
        constructor
        · intro hb
          rcases (show b = a ∨ b = Q.edge a from by simpa using hb) with rfl | rfl
          · exact hka
          · exact h
        · intro _
          have hb := hh.mp (hco a b)
          simpa using hb
      · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,hw,inv_inv,mul_one,inv_mul_cancel]
  obtain ⟨l,hnd,hm,hprod⟩ := hlocal
  have hconj' : ∀ d : D, ∃ g : K, ∀ b : E, f b = d → ¬ keep d →
      w b = g * v d * g⁻¹ := by
    intro d
    by_cases hd : ¬ keep d
    · obtain ⟨b,hb⟩ := hsurv d hd
      have hkb : ¬ keep (f b) := by rw [hb]; exact hd
      obtain ⟨g,hg⟩ := hconj b hkb
      rw [peripheral_singleton_product Q w b (hleafQ b hkb),
        peripheral_singleton_product P v (f b) (hleaf _ hkb),hb] at hg
      refine ⟨g,fun e he' _ => ?_⟩
      have heq : e = b := f.injective (he'.trans hb.symm)
      rw [heq]
      exact hg
    · exact ⟨1,fun _ _ h => (hd h).elim⟩
  choose g hg using hconj'
  refine ⟨l.map f,g,hnd.map f.injective,?_,?_⟩
  · intro d
    constructor
    · intro hd
      obtain ⟨b,hb,hbd⟩ := List.mem_map.mp hd
      rw [← hbd]
      exact (hm b).mp hb
    · intro hd
      obtain ⟨b,hb⟩ := hsurv d hd
      exact List.mem_map.mpr ⟨b,(hm b).mpr (by rw [hb]; exact hd),hb⟩
  · rw [List.map_map]
    have hh : l.map (fun b => (g (f b) * v (f b) * (g (f b))⁻¹)⁻¹) =
        l.map (fun b => (w b)⁻¹) := by
      apply List.map_congr_left
      intro b hb
      rw [← hg (f b) b rfl ((hm b).mp hb)]
    exact (congrArg List.prod hh).trans hprod

#print axioms connected_coefficient_outlet_equation



/-- Restrict to an actual connected component before compressing.
The resulting ordered relation enumerates exactly the original
peripheral darts of that component, not those of any other component. -/
theorem component_coefficient_outlet_equation {D K : Type}
    [Fintype D] [Group K] (P : RibbonMap D) (v : D → K)
    (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hleaf : ∀ d, ¬ keep d → P.rotation d = d)
    (hE : P.EulerEquality)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hint : ∀ d, keep d → cycleProduct P.rotation v d = 1)
    (o : D) (ho : ¬ keep o) :
    ∃ (l : List D) (g : D → K),
      l.Nodup ∧ (∀ d, d ∈ l ↔ P.SameComponent o d ∧ ¬ keep d) ∧
      (l.map (fun d => (g d * v d * (g d)⁻¹)⁻¹)).prod = 1 := by
  classical
  let A := {d : D // P.SameComponent o d}
  let C := P.componentRibbon o
  let a : A := ⟨o,Relation.EqvGen.refl o⟩
  have hEC : C.EulerEquality := by
    change Fintype.card (P.componentRibbon o).Vertex +
      Fintype.card (P.componentRibbon o).Face =
      Fintype.card (P.componentRibbon o).Edge +
        2 * Fintype.card (P.componentRibbon o).Component
    rw [P.componentRibbon_card_components,mul_one]
    exact P.componentRibbon_sphere hE o
  have hI (d e : A) (h : C.rotation.SameCycle d e) :
      keep d.val ↔ keep e.val :=
    hkeep _ _ ((P.restrict_sameVertex_iff (P.SameComponent o)
      (P.component_membership_edge o) (P.component_membership_rotation o) d e).mp h)
  have hleafC (d : A) (hd : ¬ keep d.val) : C.rotation d = d := by
    apply Subtype.ext
    exact hleaf d.val hd
  have hrel (d : A) (hd : keep d.val) :
      cycleProduct C.rotation (fun e : A => v e.val) d = 1 := by
    have hr := P.restrict_vertexBoundary (P.SameComponent o)
      (P.component_membership_edge o) (P.component_membership_rotation o) d
    exact (cycleProduct_of_boundary_map P C Subtype.val v d hr).trans (hint d.val hd)
  obtain ⟨l,g,hnd,hm,hprod⟩ := connected_coefficient_outlet_equation C
    (fun d : A => v d.val) (fun d : A => keep d.val) hI hleafC hEC
    (P.componentRibbon_connected o) (fun d => he d.val) hrel a ho
  let G : D → K := fun d => if h : P.SameComponent o d then g ⟨d,h⟩ else 1
  have hG (d : A) : G d.val = g d := by
    simp [G,d.property]
  refine ⟨l.map Subtype.val,G,hnd.map Subtype.val_injective,?_,?_⟩
  · intro d
    constructor
    · intro hd
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
      exact ⟨b.property,(hm b).mp hb⟩
    · rintro ⟨hc,hk⟩
      exact List.mem_map.mpr ⟨⟨d,hc⟩,(hm ⟨d,hc⟩).mpr hk,rfl⟩
  · rw [List.map_map]
    change (l.map (fun d : A => (G d.val * v d.val * (G d.val)⁻¹)⁻¹)).prod = 1
    simp only [hG]
    exact hprod

#print axioms component_coefficient_outlet_equation



/-- Specialize the complete outlet equation to the actual
coefficient-region refinement of a signed-letter ribbon. The
coefficient group is the quotient by the designated normal subgroup. -/
theorem coefficientRegions_original_outlet_equation {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hkeep : ∀ d, keep (P.rotation d) ↔ keep d)
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (o : D) (ho : ¬ keep o) :
    let S := P.coefficientRegions keep hkeep
    let v := fun d => QuotientGroup.mk' N (FreeGroup.mk [read d])
    ∃ (l : List D) (g : D → F ⧸ N), l.Nodup ∧
      (∀ d, d ∈ l ↔ S.SameComponent o d ∧ ¬ keep d) ∧
      (l.map (fun d => (g d * v d * (g d)⁻¹)⁻¹)).prod = 1 := by
  classical
  intro S v
  have hS : S.EulerEquality := P.coefficientRegions_euler keep hkeep hE
  have hstep (d : D) : keep (S.rotation d) ↔ keep d := by
    change keep ((P.coefficientRegions keep hkeep).rotation d) ↔ keep d
    rw [RibbonMap.coefficientRegions_rotation]
    split
    · exact hkeep d
    · rfl
  have hI (d e : D) (h : S.rotation.SameCycle d e) : keep d ↔ keep e := by
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    clear hn h
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.trans (hstep _).symm
  have hleaf (d : D) (hd : ¬ keep d) : S.rotation d = d := by
    change (P.coefficientRegions keep hkeep).rotation d = d
    rw [RibbonMap.coefficientRegions_rotation,ite_eq_right hd]
  have hv (d : D) : v (S.edge d) = (v d)⁻¹ := by
    change QuotientGroup.mk' N (FreeGroup.mk [read (P.edge d)]) =
      (QuotientGroup.mk' N (FreeGroup.mk [read d]))⁻¹
    rw [he,signedLetterValue_reverse,map_inv]
  have eval (l : List D) : (l.map v).prod = QuotientGroup.mk' N (FreeGroup.mk (l.map read)) := by
    induction l with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons d l ih =>
      change v d * (l.map v).prod =
        QuotientGroup.mk' N (FreeGroup.mk ([read d] ++ l.map read))
      rw [ih,← FreeGroup.mul_mk,map_mul]
  have hr (d : D) (hd : keep d) : cycleProduct S.rotation v d = 1 := by
    change ((S.vertexBoundary d).map v).prod = 1
    rw [eval,guba22_coefficient_preserved_read P read keep hkeep d hd]
    exact (QuotientGroup.eq_one_iff _).mpr (hint d hd)
  exact component_coefficient_outlet_equation S v keep hI hleaf hS hv hr o ho

/-- The outlet relation is now available in the exact lower-height
quotient for every genuine region of Guba's rank ribbon. The original
dart list and its signed letters, rather than a newly chosen spelling
of each coefficient, are retained. -/
theorem rankRibbon_coefficient_outlet_equation (pick : WeightedSelector)
    (X : ConjugatorChoice) (n j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w) :
    let P := boundaryRibbon (rankHeightRows pick X n) w s hs
    let keep := lowerRankDart pick X n j w s
    let read := discRead (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
    let N := weightedHeightStage pick X j
    ∃ hN : N.Normal, letI : N.Normal := hN
      ∃ hkeep : ∀ d, keep (P.rotation d) ↔ keep d,
        ∀ o, ¬ keep o →
          ∃ (l : List _) (g : _ → F ⧸ N), l.Nodup ∧
            (∀ d, d ∈ l ↔ (P.coefficientRegions keep hkeep).SameComponent o d ∧ ¬ keep d) ∧
            (l.map (fun d =>
              (g d * QuotientGroup.mk' N (FreeGroup.mk [read d]) * (g d)⁻¹)⁻¹)).prod = 1 := by
  intro P keep read N
  have hN : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  let : N.Normal := hN
  have hkeep : ∀ d, keep (P.rotation d) ↔ keep d := by
    intro d
    exact lowerRankDart_sameCycle pick X n j w s hs (P.rotation d) d
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  refine ⟨hN,hkeep,?_⟩
  intro o ho
  apply coefficientRegions_original_outlet_equation P read N keep hkeep
    (boundaryRibbon_euler _ w s hs) _ _ o ho
  · exact relatorRibbon_edge_read (chosenSection (Fin 2))
      (markedRows (rankHeightRows pick X n) w) (boundaryIdentity s)
      (boundaryIdentity_evaluation _ w s hs)
  · intro d hd
    obtain ⟨i,hi,hlt⟩ := hd
    exact rankRibbon_lower_vertex_mem pick X n j w s hs d i hi hlt

#print axioms coefficientRegions_original_outlet_equation
#print axioms rankRibbon_coefficient_outlet_equation



/-! ## Literal runs of outlets along an original vertex

Connectivity of the coefficient ribbon alone does not imply that its
outlets occupy a single interval on an original relator. The following
construction cuts a based traversal into maximal consecutive runs of
one coefficient component, without losing or reordering incidences.
In particular it does not assume the desired Guba contiguity coverage.
-/

/-- Extract the maximal initial run of the chosen coefficient
component. If a suffix remains, its first dart lies outside it. -/
theorem coefficient_component_prefix {D : Type} (S : RibbonMap D)
    (a : D) (l : List D) :
    ∃ p q : List D, l = p ++ q ∧
      (∀ d ∈ p, S.SameComponent a d) ∧
      (∀ b r, q = b :: r → ¬ S.SameComponent a b) := by
  classical
  induction l with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons d ds ih =>
    by_cases h : S.SameComponent a d
    · obtain ⟨p,q,he,hp,hq⟩ := ih
      refine ⟨d::p,q,?_,?_,hq⟩
      · rw [List.cons_append,← he]
      · intro e he'
        rcases List.mem_cons.mp he' with he' | he'
        · rw [he']
          exact h
        · exact hp e he'
    · refine ⟨[],d::ds,rfl,by simp,?_⟩
      intro b r he
      have hb : d = b := (List.cons.inj he).1
      rw [← hb]
      exact h

/-- Partition a based list of darts into nonempty consecutive runs,
each contained in one actual coefficient component. The first dart
of each run is its representative. Adjacent runs are in different
components, though nonadjacent runs may belong to the same one. -/
theorem coefficient_component_runs {D : Type} (S : RibbonMap D) (l : List D) :
    ∃ runs : List (D × List D),
      l = runs.flatMap (fun b => b.1 :: b.2) ∧
      (∀ b ∈ runs, ∀ d ∈ b.2, S.SameComponent b.1 d) ∧
      (∀ (p : List (D × List D)) (a b : D × List D) t,
        runs = p ++ a :: b :: t → ¬ S.SameComponent a.1 b.1) := by
  classical
  have main : ∀ n : ℕ, ∀ l : List D, l.length = n →
      ∃ runs : List (D × List D),
        l = runs.flatMap (fun b => b.1 :: b.2) ∧
        (∀ b ∈ runs, ∀ d ∈ b.2, S.SameComponent b.1 d) ∧
        (∀ (p : List (D × List D)) (a b : D × List D) t,
          runs = p ++ a :: b :: t → ¬ S.SameComponent a.1 b.1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro l hlen
      cases l with
      | nil =>
        refine ⟨[],rfl,by simp,?_⟩
        intro p a b t h
        have hlen' := congrArg List.length h
        simp at hlen'
      | cons a ds =>
        obtain ⟨p,q,he,hp,hq⟩ := coefficient_component_prefix S a ds
        have hlen' := congrArg List.length he
        simp only [List.length_append] at hlen'
        simp only [List.length_cons] at hlen
        have hlt : q.length < n := by omega
        obtain ⟨runs,hr,hs,ha⟩ := ih q.length hlt q rfl
        refine ⟨(a,p)::runs,?_,?_,?_⟩
        · simp only [List.flatMap_cons]
          rw [← hr,he]
          rfl
        · intro b hb d hd
          rcases List.mem_cons.mp hb with hb | hb
          · subst b
            exact hp d hd
          · exact hs b hb d hd
        · intro pre b c t h
          cases pre with
          | nil =>
            change (a,p)::runs = b::c::t at h
            obtain ⟨hb,ht⟩ := List.cons.inj h
            subst b
            have hqr : q = c.1 :: (c.2 ++ t.flatMap (fun b => b.1 :: b.2)) := by
              rw [hr,ht,List.flatMap_cons,List.cons_append]
            exact hq c.1 _ hqr
          | cons x xs =>
            change (a,p)::runs = x::(xs ++ b::c::t) at h
            exact ha xs b c t (List.cons.inj h).2
  exact main l.length l rfl

/-- The run partition is a literal spelling certificate: the total
weight of all the runs is exactly the weight of the original list. -/
theorem coefficient_runs_weight {D : Type} (S : RibbonMap D)
    (read : D → Letter) (l : List D) :
    ∃ runs : List (D × List D),
      l = runs.flatMap (fun b => b.1 :: b.2) ∧
      (∀ b ∈ runs, ∀ d ∈ b.2, S.SameComponent b.1 d) ∧
      (∀ (p : List (D × List D)) (a b : D × List D) t,
        runs = p ++ a :: b :: t → ¬ S.SameComponent a.1 b.1) ∧
      (runs.map (fun b => rawWeight ((b.1 :: b.2).map read))).sum =
        rawWeight (l.map read) := by
  obtain ⟨runs,hr,hs,ha⟩ := coefficient_component_runs S l
  refine ⟨runs,hr,hs,ha,?_⟩
  rw [hr]
  clear hr hs ha
  induction runs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,
      rawWeight_append]
    exact congrArg (fun n : ℕ => rawWeight (read b.1 :: b.2.map read) + n) ih

#print axioms coefficient_component_prefix
#print axioms coefficient_component_runs
#print axioms coefficient_runs_weight



/-! ## Actual cyclic interval certificates

Linear runs can be based at a transition between coefficient
components. At such a basepoint the last and first runs do not
merge across the seam. The proof uses actual permutation walks.
-/

/-- A decomposition of the departure list of a walk is a
decomposition into two genuine walks with a common endpoint. -/
theorem walk_split_departures {D : Type} (sigma : Equiv.Perm D)
    (p q : List D) (a b : D) (h : Walk sigma a b (p ++ q)) :
    ∃ c, Walk sigma a c p ∧ Walk sigma c b q := by
  induction p generalizing a with
  | nil => exact ⟨a,.nil _,h⟩
  | cons d ds ih =>
    change Walk sigma a b (d :: (ds ++ q)) at h
    cases h with
    | cons d e l ht =>
      obtain ⟨c,hp,hq⟩ := ih (sigma d) ht
      exact ⟨c,.cons _ _ _ hp,hq⟩

/-- A nonempty walk ends immediately after one of its departures. -/
theorem walk_predecessor_mem {D : Type} (sigma : Equiv.Perm D)
    {a b : D} {l : List D} (h : Walk sigma a b l) (hn : l ≠ []) :
    ∃ d ∈ l, sigma d = b := by
  induction h with
  | nil d => exact (hn rfl).elim
  | cons d e l ht ih =>
    by_cases he : l = []
    · subst l
      cases ht
      exact ⟨d,by simp,rfl⟩
    · obtain ⟨z,hz,heq⟩ := ih he
      exact ⟨z,List.mem_cons_of_mem _ hz,heq⟩

/-- If a vertex visits more than one coefficient component then it
has an actual rotation step crossing between components. -/
theorem exists_coefficient_transition {D : Type} [Finite D]
    (P S : RibbonMap D) (a b : D)
    (hab : P.rotation.SameCycle a b) (hsep : ¬ S.SameComponent a b) :
    ∃ d, P.rotation.SameCycle a d ∧
      ¬ S.SameComponent d (P.rotation d) := by
  classical
  by_contra hn
  have hs (d : D) (hd : P.rotation.SameCycle a d) :
      S.SameComponent d (P.rotation d) := by
    by_contra h
    exact hn ⟨d,hd,h⟩
  apply hsep
  obtain ⟨n,hn'⟩ := hab.exists_nat_pow_eq
  rw [← hn']
  clear hn' hab hsep
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih
      (hs _ (Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)))

/-- Basing a run partition immediately after a genuine component
transition prevents a merge across the cyclic seam. All runs remain
literal consecutive intervals of the original vertex traversal. -/
theorem cyclic_coefficient_component_runs {D : Type} [Fintype D]
    (P S : RibbonMap D) (a : D)
    (hsep : ¬ S.SameComponent a (P.rotation a)) :
    ∃ runs : List (D × List D),
      P.vertexBoundary (P.rotation a) = runs.flatMap (fun b => b.1 :: b.2) ∧
      (∀ b ∈ runs, ∀ d ∈ b.2, S.SameComponent b.1 d) ∧
      (∀ (p : List (D × List D)) (b c : D × List D) t,
        runs = p ++ b :: c :: t → ¬ S.SameComponent b.1 c.1) ∧
      (∀ (p : List (D × List D)) (b : D × List D),
        runs = p ++ [b] → ¬ S.SameComponent b.1 (P.rotation a)) := by
  obtain ⟨runs,hr,hs,ha⟩ := coefficient_component_runs S
    (P.vertexBoundary (P.rotation a))
  refine ⟨runs,hr,hs,ha,?_⟩
  intro p b hb hbad
  have hwalk : Walk P.rotation (P.rotation a) (P.rotation a)
      (P.vertexBoundary (P.rotation a)) := cycleBoundary_walk _ _
  rw [hr,hb,List.flatMap_append] at hwalk
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at hwalk
  change Walk P.rotation (P.rotation a) (P.rotation a)
    (p.flatMap (fun c => c.1 :: c.2) ++ (b.1 :: b.2)) at hwalk
  obtain ⟨z,_,hz⟩ := walk_split_departures P.rotation _ _ _ _ hwalk
  obtain ⟨d,hd,he⟩ := walk_predecessor_mem P.rotation hz (by simp)
  have hda : d = a := P.rotation.injective he
  have hmem : b ∈ runs := by rw [hb]; simp
  have hbd : S.SameComponent b.1 d := by
    rcases List.mem_cons.mp hd with h | h
    · rw [h]
      exact Relation.EqvGen.refl _
    · exact hs b hmem d h
  have hba : S.SameComponent b.1 a := hda ▸ hbd
  exact hsep (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hba) hbad)

#print axioms walk_split_departures
#print axioms walk_predecessor_mem
#print axioms exists_coefficient_transition
#print axioms cyclic_coefficient_component_runs



/-- Every indexed run of a literal vertex partition is an actual
permutation walk starting at its own representative. This bridges
the list partition to the interval-surgery infrastructure. -/
theorem vertex_run_is_walk {D : Type} [Fintype D]
    (P : RibbonMap D) (a : D)
    (runs pre post : List (D × List D)) (b : D × List D)
    (hr : P.vertexBoundary a = runs.flatMap (fun c => c.1 :: c.2))
    (hb : runs = pre ++ b :: post) :
    Walk P.rotation b.1 (P.rotation^[(b.1 :: b.2).length] b.1) (b.1 :: b.2) := by
  have hw : Walk P.rotation a a (P.vertexBoundary a) := cycleBoundary_walk _ _
  rw [hr,hb,List.flatMap_append,List.flatMap_cons] at hw
  obtain ⟨z,_,hz⟩ := walk_split_departures P.rotation _ _ _ _ hw
  obtain ⟨e,hbwalk,_⟩ := walk_split_departures P.rotation (b.1 :: b.2)
    (post.flatMap (fun c => c.1 :: c.2)) z a hz
  have hstart : z = b.1 := by
    cases hbwalk
    rfl
  subst z
  rw [hbwalk.endpoint]
  exact hbwalk

#print axioms vertex_run_is_walk



/-! ## Simultaneous geometric realization of a vertex partition

The partition of a cyclic reading into nonempty consecutive blocks
can be realized by actual vertex cuts, not merely by a list of words.
Other original vertices retain their full based readings.
-/

/-- A marked occurrence that does not appear in either prefix
determines the cut in an ordered list uniquely. -/
theorem marked_list_split_unique {D : Type} (b : D)
    (p q p' q' : List D)
    (hp : b ∉ p) (hp' : b ∉ p')
    (h : p ++ b :: q = p' ++ b :: q') :
    p = p' ∧ q = q' := by
  induction p generalizing p' with
  | nil =>
    cases p' with
    | nil => exact ⟨rfl,(List.cons.inj h).2⟩
    | cons x xs =>
      have hb : b = x := (List.cons.inj h).1
      exact (hp' (List.mem_cons.mpr (Or.inl hb))).elim
  | cons x xs ih =>
    cases p' with
    | nil =>
      have hb : x = b := (List.cons.inj h).1
      exact (hp (List.mem_cons.mpr (Or.inl hb.symm))).elim
    | cons y ys =>
      obtain ⟨hxy,ht⟩ := List.cons.inj h
      obtain ⟨hs,hq⟩ := ih ys
        (fun hm => hp (List.mem_cons_of_mem _ hm))
        (fun hm => hp' (List.mem_cons_of_mem _ hm)) ht
      exact ⟨by rw [hxy,hs],hq⟩

/-- Two nonempty successive blocks of a complete based vertex
reading are exactly the two vertex readings after a genuine cut
at their starting darts. -/
theorem vertexCut_exact_blocks {D : Type} [Fintype D]
    (P : RibbonMap D) (a b : D) (p q : List D)
    (h : P.vertexBoundary a = (a :: p) ++ (b :: q)) :
    a ≠ b ∧ P.rotation.SameCycle a b ∧
      (P.vertexCut a b).vertexBoundary a = a :: p ∧
      (P.vertexCut a b).vertexBoundary b = b :: q := by
  have hnd := cycleBoundary_nodup P.rotation a
  change (P.vertexBoundary a).Nodup at hnd
  rw [h] at hnd
  have hdis := (List.nodup_append.mp hnd).2.2
  have hnot : b ∉ a :: p := by
    intro hm
    exact hdis b hm b (by simp) rfl
  have hne : a ≠ b := by
    intro he
    exact hnot (List.mem_cons.mpr (Or.inl he.symm))
  have hsame : P.rotation.SameCycle a b := by
    apply (P.mem_vertexBoundary_iff a b).mp
    rw [h]
    exact List.mem_append.mpr (Or.inr (by simp))
  let S := P.vertexCut a b
  have hsplit : ¬ S.rotation.SameCycle a b :=
    cutAt_not_sameCycle_of_sameCycle P.rotation a b hne hsame
  have hnotS : b ∉ S.vertexBoundary a := fun hm =>
    hsplit ((S.mem_vertexBoundary_iff a b).mp hm)
  obtain ⟨t,ht⟩ := cycleBoundary_cons S.rotation b
  change S.vertexBoundary b = b :: t at ht
  have hpart := vertexCut_partition P a b hne hsame
  change P.vertexBoundary a = S.vertexBoundary a ++ S.vertexBoundary b at hpart
  rw [h,ht] at hpart
  obtain ⟨hl,hr⟩ := marked_list_split_unique b (a :: p) q
    (S.vertexBoundary a) t hnot hnotS hpart
  exact ⟨hne,hsame,hl.symm,ht.trans (congrArg (List.cons b) hr.symm)⟩

/-- A literal partition of one vertex into nonempty blocks can
be realized simultaneously by a finite sequence of actual cuts.
All original vertices outside the selected cycle remain unchanged.
In particular, this construction preserves protected lower-rank
vertices when the selected vertex is of higher rank. -/
theorem vertex_partition_splitRefinement {D : Type} [Fintype D]
    (P : RibbonMap D) (a : D) (runs : List (D × List D))
    (h : P.vertexBoundary a = runs.flatMap (fun b => b.1 :: b.2)) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (∀ b ∈ runs, (P.withRotation tau).vertexBoundary b.1 = b.1 :: b.2) ∧
      (∀ d, ¬ P.rotation.SameCycle a d →
        (P.withRotation tau).vertexBoundary d = P.vertexBoundary d) := by
  classical
  induction runs generalizing P a with
  | nil =>
    exact ((cycleBoundary_ne_nil P.rotation a) h).elim
  | cons b bs ih =>
    obtain ⟨l,hl⟩ := cycleBoundary_cons P.rotation a
    change P.vertexBoundary a = a :: l at hl
    have hb : a = b.1 := by
      rw [h,List.flatMap_cons,List.cons_append] at hl
      exact (List.cons.inj hl).1.symm
    subst a
    cases bs with
    | nil =>
      refine ⟨P.rotation,.refl _,?_,?_⟩
      · intro c hc
        have he : c = b := by simpa using hc
        subst c
        simpa only [RibbonMap.withRotation_self,List.flatMap_cons,
          List.flatMap_nil,List.append_nil] using h
      · intro d _
        rw [RibbonMap.withRotation_self]
    | cons c cs =>
      have hblocks : P.vertexBoundary b.1 =
          (b.1 :: b.2) ++ (c.1 :: (c.2 ++ cs.flatMap (fun x => x.1 :: x.2))) := by
        simpa only [List.flatMap_cons,List.cons_append] using h
      obtain ⟨hne,hcycle,hbRead,hcRead⟩ := vertexCut_exact_blocks P b.1 c.1 b.2
        (c.2 ++ cs.flatMap (fun x => x.1 :: x.2)) hblocks
      let S := P.vertexCut b.1 c.1
      have htail : S.vertexBoundary c.1 = (c::cs).flatMap (fun x => x.1 :: x.2) := by
        simpa only [List.flatMap_cons,List.cons_append] using hcRead
      obtain ⟨tau,href,hreads,hother⟩ := ih S c.1 htail
      have hsep : ¬ S.rotation.SameCycle b.1 c.1 :=
        cutAt_not_sameCycle_of_sameCycle P.rotation b.1 c.1 hne hcycle
      have href' : SplitRefinement P.rotation tau :=
        (SplitRefinement.single P.rotation b.1 c.1 hne hcycle).trans href
      have hmap : P.withRotation tau = S.withRotation tau := by
        apply RibbonMap.ext <;> rfl
      refine ⟨tau,href',?_,?_⟩
      · intro d hd
        rw [hmap]
        rcases List.mem_cons.mp hd with hd | hd
        · subst d
          exact (hother b.1 (fun he => hsep he.symm)).trans hbRead
        · exact hreads d hd
      · intro d hd
        have hn1 : ¬ P.rotation.SameCycle d b.1 := fun he => hd he.symm
        have hn2 : ¬ P.rotation.SameCycle d c.1 := fun he => hd (hcycle.trans he.symm)
        have hread : S.vertexBoundary d = P.vertexBoundary d :=
          vertexCut_other_vertex_read P b.1 c.1 d hn1 hn2
        have hnS : ¬ S.rotation.SameCycle c.1 d := by
          intro he
          have hm := (S.mem_vertexBoundary_iff d c.1).mpr he.symm
          rw [hread] at hm
          exact hn2 ((P.mem_vertexBoundary_iff d c.1).mp hm)
        rw [hmap,hother d hnS,hread]

#print axioms marked_list_split_unique
#print axioms vertexCut_exact_blocks
#print axioms vertex_partition_splitRefinement



/-- If a complete based reading is unchanged then so is membership
in its vertex cycle. This is useful when transporting the
disjointness hypotheses through successive refinements. -/
theorem sameCycle_iff_of_vertexBoundary_eq {D : Type} [Fintype D]
    (P Q : RibbonMap D) (a d : D)
    (h : Q.vertexBoundary a = P.vertexBoundary a) :
    Q.rotation.SameCycle a d ↔ P.rotation.SameCycle a d := by
  rw [← Q.mem_vertexBoundary_iff,← P.mem_vertexBoundary_iff,h]

/-- Simultaneously realize prescribed literal partitions of any
finite list of distinct original vertices. No unselected vertex
changes its based reading. In particular this permits all
lower-rank relations to remain literally unchanged. -/
theorem simultaneous_vertex_partition_splitRefinement {D : Type} [Fintype D]
    (P : RibbonMap D) (reps : List D) (blocks : D → List (D × List D))
    (hsep : reps.Pairwise (fun a b => ¬ P.rotation.SameCycle a b))
    (hpart : ∀ a ∈ reps,
      P.vertexBoundary a = (blocks a).flatMap (fun b => b.1 :: b.2)) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (∀ a ∈ reps, ∀ b ∈ blocks a,
        (P.withRotation tau).vertexBoundary b.1 = b.1 :: b.2) ∧
      (∀ d, (∀ a ∈ reps, ¬ P.rotation.SameCycle a d) →
        (P.withRotation tau).vertexBoundary d = P.vertexBoundary d) := by
  classical
  induction reps generalizing P with
  | nil =>
    refine ⟨P.rotation,.refl _,?_,?_⟩
    · intro a ha
      exact (List.not_mem_nil ha).elim
    · intro d _
      rw [RibbonMap.withRotation_self]
  | cons a as ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hsep
    obtain ⟨sigma,href,hblocks,hother⟩ :=
      vertex_partition_splitRefinement P a (blocks a) (hpart a (by simp))
    let S := P.withRotation sigma
    have hread (c : D) (hc : c ∈ as) : S.vertexBoundary c = P.vertexBoundary c :=
      hother c (hhead c hc)
    have htailS : as.Pairwise (fun c d => ¬ S.rotation.SameCycle c d) := by
      have aux : ∀ xs : List D, xs.Pairwise (fun c d => ¬ P.rotation.SameCycle c d) →
          (∀ c ∈ xs, S.vertexBoundary c = P.vertexBoundary c) →
          xs.Pairwise (fun c d => ¬ S.rotation.SameCycle c d) := by
        intro xs
        induction xs with
        | nil => intro _ _; exact .nil
        | cons c cs ih' =>
          intro hp hr
          obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hp
          apply List.pairwise_cons.mpr
          refine ⟨?_,ih' ht (fun d hd => hr d (List.mem_cons_of_mem _ hd))⟩
          intro d hd hs
          exact hh d hd ((sameCycle_iff_of_vertexBoundary_eq P S c d (hr c (by simp))).mp hs)
      exact aux as htail hread
    have hpartS (c : D) (hc : c ∈ as) :
        S.vertexBoundary c = (blocks c).flatMap (fun b => b.1 :: b.2) :=
      (hread c hc).trans (hpart c (List.mem_cons_of_mem _ hc))
    obtain ⟨tau,hrefS,htblocks,htother⟩ := ih S htailS hpartS
    have hmap : P.withRotation tau = S.withRotation tau := by
      apply RibbonMap.ext <;> rfl
    refine ⟨tau,href.trans hrefS,?_,?_⟩
    · intro c hc b hb
      rw [hmap]
      rcases List.mem_cons.mp hc with he | he
      · subst c
        have hba : P.rotation.SameCycle a b.1 := by
          apply (P.mem_vertexBoundary_iff a b.1).mp
          rw [hpart a (by simp)]
          exact List.mem_flatMap.mpr ⟨b,hb,by simp⟩
        have hprotect (d : D) (hd : d ∈ as) : ¬ S.rotation.SameCycle d b.1 := by
          intro h
          have hold := (sameCycle_iff_of_vertexBoundary_eq P S d b.1 (hread d hd)).mp h
          exact hhead d hd (hba.trans hold.symm)
        exact (htother b.1 hprotect).trans (hblocks b hb)
      · exact htblocks c he b hb
    · intro d hd
      have hr : S.vertexBoundary d = P.vertexBoundary d := hother d (hd a (by simp))
      have hprotect (c : D) (hc : c ∈ as) : ¬ S.rotation.SameCycle c d := by
        intro h
        exact hd c (List.mem_cons_of_mem _ hc)
          ((sameCycle_iff_of_vertexBoundary_eq P S c d (hread c hc)).mp h)
      rw [hmap,htother d hprotect,hr]

/-- If every selected vertex is outside a cycle-invariant protected
set, all protected vertex readings remain unchanged by the simultaneous
refinement. The sphere Euler equality is inherited from the original. -/
theorem protected_simultaneous_vertex_partitions {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop) (reps : List D)
    (blocks : D → List (D × List D))
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hselected : ∀ a ∈ reps, ¬ keep a)
    (hsep : reps.Pairwise (fun a b => ¬ P.rotation.SameCycle a b))
    (hpart : ∀ a ∈ reps,
      P.vertexBoundary a = (blocks a).flatMap (fun b => b.1 :: b.2))
    (hE : P.EulerEquality) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (P.withRotation tau).EulerEquality ∧
      (∀ a ∈ reps, ∀ b ∈ blocks a,
        (P.withRotation tau).vertexBoundary b.1 = b.1 :: b.2) ∧
      (∀ d, keep d → (P.withRotation tau).vertexBoundary d = P.vertexBoundary d) := by
  obtain ⟨tau,href,hreads,hother⟩ :=
    simultaneous_vertex_partition_splitRefinement P reps blocks hsep hpart
  refine ⟨tau,href,P.splitRefinement_preserves_euler href hE,hreads,?_⟩
  intro d hd
  apply hother d
  intro a ha h
  exact hselected a ha ((hkeep a d h).mpr hd)

#print axioms sameCycle_iff_of_vertexBoundary_eq
#print axioms simultaneous_vertex_partition_splitRefinement
#print axioms protected_simultaneous_vertex_partitions



/-! ## Connectivity of the simultaneous interval refinement

Grouping consecutive singleton outlets of one coefficient component
does not change its component. The following theorem proves the
component correspondence on the original dart type, retaining the
protected vertices and the actual rotation cuts.
-/

/-- Component comparison can be proved on the actual generators of
the connectivity relation, namely edge and rotation steps. -/
theorem ribbon_component_of_steps {D : Type} (P Q : RibbonMap D)
    (he : ∀ d, Q.SameComponent d (P.edge d))
    (hr : ∀ d, Q.SameComponent d (P.rotation d))
    {a b : D} (h : P.SameComponent a b) : Q.SameComponent a b := by
  induction h with
  | rel x y h =>
    rcases h with h | h
    · rw [← h]
      exact he x
    · rw [← h]
      exact hr x
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- When every peripheral vertex is partitioned into blocks lying
in single coefficient components, the simultaneous geometric
refinement has exactly the same connected components as the
singleton coefficient refinement. No components are merged or lost. -/
theorem coefficient_partition_sameComponent {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
    (reps : List D) (blocks : D → List (D × List D))
    (hselected : ∀ a ∈ reps, ¬ keep a)
    (hcov : ∀ d, ¬ keep d → ∃ a ∈ reps, P.rotation.SameCycle a d)
    (hsep : reps.Pairwise (fun a b => ¬ P.rotation.SameCycle a b))
    (hpart : ∀ a ∈ reps,
      P.vertexBoundary a = (blocks a).flatMap (fun b => b.1 :: b.2))
    (hlocal : ∀ a ∈ reps, ∀ b ∈ blocks a, ∀ d ∈ b.2,
      (P.coefficientRegions keep hstep).SameComponent b.1 d)
    (hE : P.EulerEquality) :
    ∃ tau : Equiv.Perm D, SplitRefinement P.rotation tau ∧
      (P.withRotation tau).EulerEquality ∧
      (∀ a ∈ reps, ∀ b ∈ blocks a,
        (P.withRotation tau).vertexBoundary b.1 = b.1 :: b.2) ∧
      (∀ d, keep d → (P.withRotation tau).vertexBoundary d = P.vertexBoundary d) ∧
      (∀ d e, (P.withRotation tau).SameComponent d e ↔
        (P.coefficientRegions keep hstep).SameComponent d e) := by
  classical
  obtain ⟨tau,href,hEuler,hread,hprotected⟩ :=
    protected_simultaneous_vertex_partitions P keep reps blocks hkeep hselected hsep hpart hE
  let Q := P.withRotation tau
  let S := P.coefficientRegions keep hstep
  have hSread (d : D) (hd : keep d) : S.vertexBoundary d = P.vertexBoundary d := by
    change (P.withRotation S.rotation).vertexBoundary d = P.vertexBoundary d
    apply refined_vertex_read_of_agreement
    intro e he
    have hk := (hkeep d e he).mp hd
    change (P.coefficientRegions keep hstep).rotation e = P.rotation e
    rw [RibbonMap.coefficientRegions_rotation,ite_eq_left hk]
  have hQtoS (d : D) : S.SameComponent d (Q.rotation d) := by
    by_cases hd : keep d
    · have hr : Q.vertexBoundary d = S.vertexBoundary d :=
        (hprotected d hd).trans (hSread d hd).symm
      have hcyc : Q.rotation.SameCycle d (Q.rotation d) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      exact S.component_of_vertexCycle
        ((sameCycle_iff_of_vertexBoundary_eq S Q d (Q.rotation d) hr).mp hcyc)
    · obtain ⟨a,ha,had⟩ := hcov d hd
      have hm := (P.mem_vertexBoundary_iff a d).mpr had
      rw [hpart a ha] at hm
      obtain ⟨b,hb,hdb⟩ := List.mem_flatMap.mp hm
      have hbRead : Q.vertexBoundary b.1 = b.1 :: b.2 := hread a ha b hb
      have hc : Q.rotation.SameCycle b.1 d :=
        (Q.mem_vertexBoundary_iff _ _).mp (hbRead.symm ▸ hdb)
      have hnext : Q.rotation.SameCycle b.1 (Q.rotation d) :=
        Equiv.Perm.sameCycle_apply_right.mpr hc
      have hmem : Q.rotation d ∈ b.1 :: b.2 := by
        rw [← hbRead]
        exact (Q.mem_vertexBoundary_iff _ _).mpr hnext
      have hlocal' (e : D) (he : e ∈ b.1 :: b.2) : S.SameComponent b.1 e := by
        rcases List.mem_cons.mp he with he | he
        · rw [he]
          exact Relation.EqvGen.refl _
        · exact hlocal a ha b hb e he
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hlocal' d hdb))
        (hlocal' _ hmem)
  have hStoQ (d : D) : Q.SameComponent d (S.rotation d) := by
    by_cases hd : keep d
    · have hr : S.vertexBoundary d = Q.vertexBoundary d :=
        (hSread d hd).trans (hprotected d hd).symm
      have hcyc : S.rotation.SameCycle d (S.rotation d) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      exact Q.component_of_vertexCycle
        ((sameCycle_iff_of_vertexBoundary_eq Q S d (S.rotation d) hr).mp hcyc)
    · have hf : S.rotation d = d := by
        change (P.coefficientRegions keep hstep).rotation d = d
        rw [RibbonMap.coefficientRegions_rotation,ite_eq_right hd]
      rw [hf]
      exact Relation.EqvGen.refl _
  refine ⟨tau,href,hEuler,hread,hprotected,?_⟩
  intro d e
  exact ⟨ribbon_component_of_steps Q S (fun x => S.component_edge x) hQtoS,
    ribbon_component_of_steps S Q (fun x => Q.component_edge x) hStoQ⟩

#print axioms ribbon_component_of_steps
#print axioms coefficient_partition_sameComponent



/-! ## Existence of a global interval refinement

Choose representatives of the original peripheral vertices and their
literal coefficient-component runs. The simultaneous refinement is
therefore obtained from the given diagram, without supplying a
representative list or a block partition as additional premises.
-/

/-- From any finite list choose one representative of each rotation
cycle that meets it, with no duplication of cycles. -/
theorem vertex_cycle_representatives {D : Type} (P : RibbonMap D)
    (l : List D) :
    ∃ reps : List D, (∀ a ∈ reps, a ∈ l) ∧
      reps.Pairwise (fun a b => ¬ P.rotation.SameCycle a b) ∧
      (∀ d ∈ l, ∃ a ∈ reps, P.rotation.SameCycle a d) := by
  classical
  induction l with
  | nil =>
    exact ⟨[],by simp,.nil,by simp⟩
  | cons d ds ih =>
    obtain ⟨reps,hsub,hsep,hcov⟩ := ih
    by_cases h : ∃ a ∈ reps, P.rotation.SameCycle a d
    · refine ⟨reps,fun a ha => List.mem_cons_of_mem _ (hsub a ha),hsep,?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]
        exact h
      · exact hcov e he
    · refine ⟨d :: reps,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with ha | ha
        · rw [ha]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a ha)
      · apply List.pairwise_cons.mpr
        exact ⟨fun a ha hc => h ⟨a,ha,hc.symm⟩,hsep⟩
      · intro e he
        rcases List.mem_cons.mp he with he | he
        · rw [he]
          exact ⟨d,List.mem_cons_self,.refl _ _⟩
        · obtain ⟨a,ha,hd⟩ := hcov e he
          exact ⟨a,List.mem_cons_of_mem _ ha,hd⟩

/-- The interval refinement exists for every finite spherical
ribbon and every cycle-invariant protected set. All peripheral
darts are covered by the literal runs of their original vertices;
the genuine coefficient components and protected words are
unchanged. Runs are based linear intervals; this statement does
not assert metric coverage by Guba's preferred contiguity bands. -/
theorem exists_global_coefficient_interval_refinement {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d e, P.rotation.SameCycle d e → (keep d ↔ keep e))
    (hE : P.EulerEquality) :
    ∃ (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
      (reps : List D) (blocks : D → List (D × List D))
      (tau : Equiv.Perm D),
      (∀ a ∈ reps, ¬ keep a) ∧
      (∀ d, ¬ keep d → ∃ a ∈ reps, P.rotation.SameCycle a d) ∧
      reps.Pairwise (fun a b => ¬ P.rotation.SameCycle a b) ∧
      (∀ a ∈ reps, P.vertexBoundary a =
        (blocks a).flatMap (fun b => b.1 :: b.2)) ∧
      (∀ a ∈ reps, ∀ b ∈ blocks a, ∀ d ∈ b.2,
        (P.coefficientRegions keep hstep).SameComponent b.1 d) ∧
      SplitRefinement P.rotation tau ∧
      (P.withRotation tau).EulerEquality ∧
      (∀ a ∈ reps, ∀ b ∈ blocks a,
        (P.withRotation tau).vertexBoundary b.1 = b.1 :: b.2) ∧
      (∀ d, keep d → (P.withRotation tau).vertexBoundary d = P.vertexBoundary d) ∧
      (∀ d e, (P.withRotation tau).SameComponent d e ↔
        (P.coefficientRegions keep hstep).SameComponent d e) := by
  classical
  have hstep (d : D) : keep (P.rotation d) ↔ keep d :=
    hkeep _ _ (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
  let B := Finset.univ.filter (fun d : D => ¬ keep d)
  have hB (d : D) : d ∈ B.toList ↔ ¬ keep d := by
    simp [B]
  obtain ⟨reps,hsub,hsep,hcov⟩ := vertex_cycle_representatives P B.toList
  let S := P.coefficientRegions keep hstep
  have hchoose (a : D) : ∃ runs : List (D × List D),
      P.vertexBoundary a = runs.flatMap (fun b => b.1 :: b.2) ∧
      (∀ b ∈ runs, ∀ d ∈ b.2, S.SameComponent b.1 d) := by
    obtain ⟨runs,hr,hs,_⟩ := coefficient_component_runs S (P.vertexBoundary a)
    exact ⟨runs,hr,hs⟩
  choose blocks hpart hlocal using hchoose
  have hsel (a : D) (ha : a ∈ reps) : ¬ keep a := (hB a).mp (hsub a ha)
  have hcover (d : D) (hd : ¬ keep d) : ∃ a ∈ reps, P.rotation.SameCycle a d :=
    hcov d ((hB d).mpr hd)
  obtain ⟨tau,href,hEuler,hread,hprotected,hcomp⟩ :=
    coefficient_partition_sameComponent P keep hkeep hstep reps blocks
      hsel hcover hsep (fun a _ => hpart a) (fun a _ => hlocal a) hE
  exact ⟨hstep,reps,blocks,tau,hsel,hcover,hsep,fun a _ => hpart a,
    fun a _ => hlocal a,href,hEuler,hread,hprotected,hcomp⟩

#print axioms vertex_cycle_representatives
#print axioms exists_global_coefficient_interval_refinement



/-! ## Induction on graded diagram type

Guba, Math. USSR Izv. 29 (1987), pp. 251--259, uses simultaneous
induction for Lemmas 13--25. A rank-minimal expression for one fixed
word does not provide that induction hypothesis: a subdiagram
generally has a different boundary. Use descending lexicographic
counts over an arbitrary family of objects instead.

This does not identify the component-run refinement with the
preferred contiguity subdiagrams in the paper. In particular the
bond construction and the metric estimates for the connecting
sides still require proofs.
-/

/-- Descending lexicographic strict comparison of finite rank
profiles, with no bound on lower coordinates. -/
def descendingCountLT {A : Type} (n : ℕ) (count : A → ℕ → ℕ)
    (t s : A) : Prop :=
  ∃ j < n, count t j < count s j ∧
    ∀ k, j < k → k < n → count t k = count s k

/-- Induction over all objects of smaller graded type, independent
of their boundary values. Several statements may be proved
simultaneously by taking the predicate to be their conjunction. -/
theorem descending_count_induction {A : Type} (n : ℕ)
    (count : A → ℕ → ℕ) (P : A → Prop)
    (step : ∀ s, (∀ t, descendingCountLT n count t s → P t) → P s) :
    ∀ s, P s := by
  classical
  by_contra h
  push Not at h
  obtain ⟨s,hs,hmin⟩ := exists_descending_count_min n
    (fun s => ¬ P s) count h
  apply hs
  apply step s
  intro t ht
  by_contra hn
  obtain ⟨j,hj,hlt,habove⟩ := ht
  exact (Nat.not_lt_of_ge (hmin t hn j hj
    (fun k hjk hkn => (habove k hjk hkn).symm))) hlt

/-- A literal sublist cannot increase the count at any rank. -/
theorem rankCount_le_of_sublist {n : ℕ}
    {s t : Peiffer.Sequence F (RankHeight n)} (h : s.Sublist t) (j : ℕ) :
    rankCount s j ≤ rankCount t j := by
  unfold rankCount
  exact (h.filter (fun x => decide (x.1.2.1.val = j))).length_le

/-- If one of the coordinates decreases and none increases,
the finite descending profile strictly decreases. Choose the
highest changed coordinate, rather than imposing a bound on
the total number of lower-rank cells. -/
theorem descending_count_lt_of_pointwise {A : Type} (n : ℕ)
    (count : A → ℕ → ℕ) (t s : A)
    (hle : ∀ j < n, count t j ≤ count s j)
    (hlt : ∃ j < n, count t j < count s j) :
    descendingCountLT n count t s := by
  classical
  induction n with
  | zero =>
    obtain ⟨j,hj,_⟩ := hlt
    omega
  | succ n ih =>
    by_cases hn : count t n < count s n
    · exact ⟨n,Nat.lt_succ_self _,hn,fun k hk hkn => by omega⟩
    · have he : count t n = count s n :=
        Nat.le_antisymm (hle n (Nat.lt_succ_self _)) (Nat.le_of_not_gt hn)
      have hlt' : ∃ j < n, count t j < count s j := by
        obtain ⟨j,hj,hstrict⟩ := hlt
        have hj' : j < n := by
          by_contra hh
          have hjn : j = n := by omega
          rw [hjn,he] at hstrict
          omega
        exact ⟨j,hj',hstrict⟩
      obtain ⟨j,hj,hstrict,habove⟩ := ih
        (fun k hk => hle k (Nat.lt_succ_of_lt hk)) hlt'
      refine ⟨j,Nat.lt_succ_of_lt hj,hstrict,?_⟩
      intro k hjk hkn
      by_cases hk : k = n
      · rw [hk,he]
      · exact habove k hjk (by omega)

/-- Removing a specified occurrence and keeping an arbitrary
sublist of the other occurrences strictly lowers the rank type,
even if the removed occurrence does not have maximal rank. -/
theorem rank_type_lt_of_omitted_occurrence {n : ℕ}
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (t : Peiffer.Sequence F (RankHeight n))
    (h : t.Sublist (p ++ r)) :
    descendingCountLT n rankCount t (p ++ [x] ++ r) := by
  apply descending_count_lt_of_pointwise
  · intro j _
    have hj := rankCount_le_of_sublist h j
    rw [rankCount_append] at hj
    simp only [rankCount_append]
    omega
  · refine ⟨x.1.2.1.val,x.1.2.1.isLt,?_⟩
    have hj := rankCount_le_of_sublist h x.1.2.1.val
    rw [rankCount_append] at hj
    simp only [rankCount_append,rankCount_singleton,ite_true]
    omega

#print axioms descendingCountLT
#print axioms descending_count_induction
#print axioms rankCount_le_of_sublist
#print axioms descending_count_lt_of_pointwise
#print axioms rank_type_lt_of_omitted_occurrence



/-! ## Numerical dependency audit for Lemmas 13 and 19

The English text of Lemma 19, p. 253, has 4000 omega (twice
2000 omega), not 400 omega. The earlier arithmetic theorem is
corrected above to use the actual weaker premise. Here its premise
is derived explicitly from the separate nine-category inequalities.
The geometric validity of those inequalities is not assumed as an
axiom and remains to be proved.

In Lemma 13, p. 251, the displayed parameter comparison appears
inconsistent with the parameter table as transcribed from the
English text. Record the exact rational squared comparison rather
than silently changing the chosen parameters. This is a check of
the displayed bound, not a refutation of Lemma 13 or the paper.
-/

/-- The numerical assembly of Lemma 19 from the individual
category estimates in Lemmas 8--18. In particular the special-cell
contribution occurs twice, once in H0 and once in P. -/
theorem guba19_from_nine_categories (V M N K D E F H0 P K0 G0 D0 : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (htotal : V = M + N)
    (hpartition : M ≤ K+D+E+F+H0+P+K0+G0+D0)
    (hbase : K+D+E+F ≤ (1-99/100)*V)
    (h14 : H0 ≤ 2000*(1/10^7)*V)
    (h15 : K0 ≤ 450*(1/10^17 : ℝ)^(1/2 : ℝ)*V)
    (h16 : G0 ≤ (8/15)*M)
    (h17 : D0 ≤ 2*(1/10^7 : ℝ)^(1/2 : ℝ)*M)
    (h18 : P ≤ 300*(1/10^11 : ℝ)^(1/2 : ℝ)*M + H0) :
    (95/100 + 300*(1/10^7 : ℝ)^(3/2 : ℝ))*V ≤ N := by
  have hMV : M ≤ V := by linarith
  have hcoeff : 0 ≤ 300*(1/10^11 : ℝ)^(1/2 : ℝ) := by positivity
  have h18' : P ≤ 300*(1/10^11 : ℝ)^(1/2 : ℝ)*V + H0 :=
    h18.trans (add_le_add (mul_le_mul_of_nonneg_left hMV hcoeff) (le_refl H0))
  apply guba19_outer_weight_arithmetic V M N hM hN htotal
  linarith only [hpartition,hbase,h14,h15,h16,h17,h18']

/-- With the parameters as transcribed, the square of the
coefficient used in the short-section case of Lemma 13 is greater
than omega cubed, not smaller. All arithmetic is exact. -/
theorem guba13_transcribed_parameter_square_check :
    (1/10^7 : ℚ)^3 <
      (3*10^11 * ((9/10 : ℚ)*(1/10^17)-2*(1/10^19))⁻¹ *
        (1/10^38))^2 := by
  norm_num

/-- The purely linear part of the Lemma 13 argument, retaining
the exact coefficient without replacing it by omega^(3/2).
The assumptions are the long-section, contiguity, connecting-side,
and lower-type transfer bounds, in a common length scale. -/
theorem guba13_short_section_exact_bound (P L q1 q2 p1 p2 B : ℚ)
    (hP : P < 3*10^11*L)
    (hdegree : (1/10^17 : ℚ)*L ≤ q1)
    (hsides : p1+p2 ≤ 2*(1/10^19)*L)
    (htransfer : (9/10 : ℚ)*q1 ≤ p1+p2+q2)
    (hshort : q2 ≤ (1/10^38 : ℚ)*B) :
    P < (3*10^11 * ((9/10 : ℚ)*(1/10^17)-2*(1/10^19))⁻¹ *
        (1/10^38))*B := by
  have hL : ((9/10 : ℚ)*(1/10^17)-2*(1/10^19))*L ≤
      (1/10^38 : ℚ)*B := by
    linarith only [hdegree,hsides,htransfer,hshort]
  norm_num at hL hP ⊢
  linarith only [hL,hP]

#print axioms guba19_from_nine_categories
#print axioms guba13_transcribed_parameter_square_check
#print axioms guba13_short_section_exact_bound



/-! ## Repair of the local numerical budget without changing the presentation

The scan of the Russian original (Izv. Akad. Nauk SSSR 50 (1986),
pp. 883, 900, 902, 906) confirms the parameters and the inequality
in Lemma 13. Only the boundary-to-cell estimate needs a larger
constant here: take c = 1/1000 and use c^3 in place of omega^(3/2)
in the applications of Lemma 13. Keep omega itself unchanged in
all earlier lemmas. The following conditional arithmetic lemmas
check the resulting budget for Lemmas 14, 17--19 and 22.
The preferred contiguity system and the geometric input bounds
are still obligations, not established by this numerical repair.
-/

/-- Both boundary-section cases of Lemma 13 satisfy the relaxed
perimeter bound, even including the first-kind factor 1+epsilon. -/
theorem guba13_relaxed_bound (P L q1 q2 p1 p2 B : ℚ)
    (hB : 0 ≤ B)
    (hP : P < 3*10^11*L)
    (hdegree : (1/10^17 : ℚ)*L ≤ q1)
    (hsides : p1+p2 ≤ 2*(1/10^19)*L)
    (htransfer : (9/10 : ℚ)*q1 ≤ p1+p2+q2)
    (hshort : q2 ≤ (1+1/120)*(1/10^38 : ℚ)*B) :
    P < (1/1000 : ℚ)^3 * B := by
  norm_num at hP hdegree hsides htransfer hshort ⊢
  linarith only [hB,hP,hdegree,hsides,htransfer,hshort]

/-- The relaxed principal-cell weight bound, with the unchanged
cell-to-cell contributions in Lemma 14. -/
theorem guba14_relaxed_budget (V Hcell Hmixed Hboundary : ℝ)
    (hV : 0 ≤ V)
    (hcell : Hcell ≤ 300*(1/10^7)*V)
    (hmixed : Hmixed ≤ 450*(1/10^7)*V)
    (hboundary : Hboundary ≤ 2*12^2*3*(1/1000 : ℝ)^2*V) :
    Hcell+Hmixed+Hboundary ≤ (1/1000 : ℝ)*V := by
  norm_num at hcell hmixed hboundary ⊢
  linarith only [hV,hcell,hmixed,hboundary]

/-- The two numerical factors needed for Lemmas 17 and 18 remain
valid with the relaxed boundary constant. -/
theorem guba17_18_relaxed_factors :
    (9/10 : ℝ)⁻¹*(1+2*(1/10^19)*(1/10^17)⁻¹) < 2 ∧
    (9/10 : ℝ)⁻¹*(1/1000) ≤ 1 := by
  norm_num

/-- With the relaxed bounds for H0 and D0 the outer weight is still
at least 96 percent. The nine-category partition is a geometric
hypothesis. No change to the group parameters is made. -/
theorem guba19_relaxed_budget (V M N K D E F H0 P K0 G0 D0 : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (htotal : V = M+N)
    (hpartition : M ≤ K+D+E+F+H0+P+K0+G0+D0)
    (hbase : K+D+E+F ≤ (1-99/100)*V)
    (h14 : H0 ≤ (1/1000 : ℝ)*V)
    (h15 : K0 ≤ 450*(1/10^17 : ℝ)^(1/2 : ℝ)*V)
    (h16 : G0 ≤ (8/15)*M)
    (h17 : D0 ≤ 2*(1/1000 : ℝ)*M)
    (h18 : P ≤ 300*(1/10^11 : ℝ)^(1/2 : ℝ)*M + H0) :
    (96/100 : ℝ)*V ≤ N := by
  have root_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hxy : x ≤ y^2) : x^(1/2 : ℝ) ≤ y := by
    have h := Real.rpow_le_rpow hx hxy (by norm_num : 0 ≤ (1/2 : ℝ))
    rw [← Real.rpow_natCast_mul hy 2 (1/2 : ℝ)] at h
    norm_num at h
    exact h
  have hV : 0 ≤ V := by linarith
  have hb : (1/10^17 : ℝ)^(1/2 : ℝ) ≤ 1/10^8 :=
    root_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have ht : (1/10^11 : ℝ)^(1/2 : ℝ) ≤ 1/200000 :=
    root_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have hK : K0 ≤ 450*(1/10^8 : ℝ)*V :=
    h15.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by norm_num)) hV)
  have hP : P ≤ 300*(1/200000 : ℝ)*M + H0 :=
    h18.trans (add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 300)) hM) (le_refl H0))
  norm_num at hbase h14 hK hP h16 h17 ⊢
  linarith only [hpartition,hbase,h14,hK,hP,h16,h17,htotal,hV,hM]

/-- A first-to-second-kind arc remains sufficiently short even
counting BOTH connecting sides in Lemma 22. -/
theorem guba22_relaxed_arc_bound (B q1 q2 p1 p2 : ℚ)
    (hB : 0 ≤ B)
    (hsecond : q2 ≤ (1/10^38 : ℚ)*B)
    (hside1 : p1 ≤ (1+2*(1/10^19 : ℚ))*(1/1000 : ℚ)^3*B)
    (hside2 : p2 ≤ (1+2*(1/10^19 : ℚ))*(1/1000 : ℚ)^3*B)
    (htransfer : (9/10 : ℚ)*q1 ≤ q2+p1+p2) :
    q1 ≤ 3*(1/1000 : ℚ)^3*B := by
  norm_num at hsecond hside1 hside2 htransfer ⊢
  linarith only [hB,hsecond,hside1,hside2,htransfer]

/-- The loss from at most 2*6*12 excluded arcs fits into the
relaxed outer-weight margin. This is only the numerical final
step of Lemma 22, conditional on the actual disjoint coverage
and multiplicity estimates in a common length scale. -/
theorem guba22_relaxed_pruning_budget (B total bad good : ℚ)
    (hB : 0 ≤ B)
    (htotal : (96/100 : ℚ)*B ≤ total)
    (hbad : bad ≤ 2*6*12*3*(1/1000 : ℚ)^3*B)
    (hsplit : total ≤ good+bad) :
    (95/100 : ℚ)*B ≤ good := by
  norm_num at htotal hbad ⊢
  linarith only [hB,htotal,hbad,hsplit]

#print axioms guba13_relaxed_bound
#print axioms guba14_relaxed_budget
#print axioms guba17_18_relaxed_factors
#print axioms guba19_relaxed_budget
#print axioms guba22_relaxed_arc_bound
#print axioms guba22_relaxed_pruning_budget



/-! ## Final perimeter transfer using actual dart supports

For the numerical estimate in Lemma 23 the outer arcs need not be
provided in a common boundary order. Disjointness of their actual
dart supports, together with membership in the marked boundary
cycle, suffices. Repeated letters do not identify distinct darts.
The number of corridors and the local transfer bounds remain
geometric obligations.
-/

theorem dart_read_weight_sum {D : Type} [DecidableEq D]
    (read : D → Letter) (l : List D) (hnd : l.Nodup) :
    rawWeight (l.map read) = ∑ d ∈ l.toFinset, letterWeight (read d) := by
  have eval (ds : List D) :
      rawWeight (ds.map read) = (ds.map (fun d => letterWeight (read d))).sum := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      change letterWeight (read d) + rawWeight (ds.map read) =
        letterWeight (read d) + (ds.map (fun d => letterWeight (read d))).sum
      rw [ih]
  rw [eval, List.sum_toFinset _ hnd]

/-- Disjoint actual dart lists in a single vertex can be summed in
any order. This replaces the stronger literal-sublist certificate. -/
theorem guba23_disjoint_dart_arcs_weight {A D : Type} [Fintype D] [DecidableEq D]
    (P : RibbonMap D) (read : D → Letter) (z : D)
    (arcs : Finset A) (outer : A → List D)
    (hnd : ∀ a ∈ arcs, (outer a).Nodup)
    (hdis : Set.PairwiseDisjoint (↑arcs : Set A) (fun a => (outer a).toFinset))
    (hcycle : ∀ a ∈ arcs, ∀ d ∈ outer a, P.rotation.SameCycle z d) :
    (∑ a ∈ arcs, rawWeight ((outer a).map read)) ≤
      rawWeight ((P.vertexBoundary z).map read) := by
  classical
  have hs : arcs.biUnion (fun a => (outer a).toFinset) ⊆
      (P.vertexBoundary z).toFinset := by
    intro d hd
    obtain ⟨a,ha,hd'⟩ := Finset.mem_biUnion.mp hd
    exact List.mem_toFinset.mpr ((P.mem_vertexBoundary_iff z d).mpr
      (hcycle a ha d (List.mem_toFinset.mp hd')))
  calc
    _ = ∑ a ∈ arcs, ∑ d ∈ (outer a).toFinset, letterWeight (read d) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact dart_read_weight_sum read (outer a) (hnd a ha)
    _ = ∑ d ∈ arcs.biUnion (fun a => (outer a).toFinset), letterWeight (read d) := by
      rw [Finset.sum_biUnion hdis]
    _ ≤ ∑ d ∈ (P.vertexBoundary z).toFinset, letterWeight (read d) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    _ = _ := (dart_read_weight_sum read _ (P.vertexBoundary_nodup z)).symm

/-- The six-corridor version of the final transfer estimate.
The left lengths are kept independently of the right dart lists;
their identification with the inner arc readings is a local
geometric obligation. -/
theorem guba23_dart_boundary_transfer {A D : Type} [Fintype D] [DecidableEq D]
    (P : RibbonMap D) (read : D → Letter) (z : D)
    (arcs : Finset A) (inner : A → ℕ) (outer : A → List D)
    (L : ℚ) (hL : 0 ≤ L) (hcount : arcs.card ≤ 6)
    (hnd : ∀ a ∈ arcs, (outer a).Nodup)
    (hdis : Set.PairwiseDisjoint (↑arcs : Set A) (fun a => (outer a).toFinset))
    (hcycle : ∀ a ∈ arcs, ∀ d ∈ outer a, P.rotation.SameCycle z d)
    (hlocal : ∀ a ∈ arcs, (9/10 : ℚ) * (inner a : ℚ) -
      (2/10^19 : ℚ) * L ≤ (rawWeight ((outer a).map read) : ℚ)) :
    (9/10 : ℚ) * (∑ a ∈ arcs, (inner a : ℚ)) -
      (12/10^19 : ℚ) * L ≤ (rawWeight ((P.vertexBoundary z).map read) : ℚ) := by
  have ht : (∑ a ∈ arcs, ((9/10 : ℚ) * (inner a : ℚ) -
        (2/10^19 : ℚ) * L)) ≤
      ∑ a ∈ arcs, (rawWeight ((outer a).map read) : ℚ) :=
    Finset.sum_le_sum hlocal
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at ht
  have hb := guba23_disjoint_dart_arcs_weight P read z arcs outer hnd hdis hcycle
  have hbQ : (∑ a ∈ arcs, (rawWeight ((outer a).map read) : ℚ)) ≤
      (rawWeight ((P.vertexBoundary z).map read) : ℚ) := by exact_mod_cast hb
  have hc : (arcs.card : ℚ) ≤ 6 := by exact_mod_cast hcount
  have he : 0 ≤ (2/10^19 : ℚ) * L := mul_nonneg (by norm_num) hL
  have herr := mul_le_mul_of_nonneg_right hc he
  linarith only [ht,hbQ,herr]

/-- Strictness of the final perimeter estimate follows from the
numerical margin even with non-strict retained coverage. -/
theorem guba23_perimeter_arithmetic_six (P D C B : ℚ)
    (hP : 0 < P)
    (hD : (1 - 1 / 10^80) * P ≤ D)
    (hcover : (95/100 - 18/10^11) * D ≤ C)
    (htransfer : (9/10) * C - (12/10^19) * P ≤ B) :
    (4/5) * P < B := by
  norm_num at hD hcover htransfer ⊢
  linarith

/-- The weight of the marked boundary is the actual weighted length
of the boundary element; no cyclic-order certificate for the outer
arcs is needed. -/
theorem guba23_marked_boundary_transfer_darts {A : Type}
    (rows : I → RawWord) (w : F) (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) (arcs : Finset A) (inner : A → ℕ)
    [DecidableEq (DiscDarts (markedRows rows w) (boundaryIdentity s))]
    (outer : A → List (DiscDarts (markedRows rows w) (boundaryIdentity s)))
    (L : ℚ) (hL : 0 ≤ L) (hcount : arcs.card ≤ 6)
    (hnd : ∀ a ∈ arcs, (outer a).Nodup)
    (hdis : Set.PairwiseDisjoint (↑arcs : Set A) (fun a => (outer a).toFinset))
    (hcycle : ∀ a ∈ arcs, ∀ d ∈ outer a,
      (boundaryRibbon rows w s hs).rotation.SameCycle (boundaryDart rows w s hw) d)
    (hlocal : ∀ a ∈ arcs, (9/10 : ℚ) * (inner a : ℚ) -
      (2/10^19 : ℚ) * L ≤ (rawWeight ((outer a).map
        (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) : ℚ)) :
    (9/10 : ℚ) * (∑ a ∈ arcs, (inner a : ℚ)) -
      (12/10^19 : ℚ) * L ≤ (weightedLength w : ℚ) := by
  classical
  have h := guba23_dart_boundary_transfer (boundaryRibbon rows w s hs)
    (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))
    (boundaryDart rows w s hw) arcs inner outer L hL hcount hnd hdis hcycle hlocal
  rw [boundaryRibbon_read rows w s hs hw,rawWeight_invRev] at h
  exact h

#print axioms dart_read_weight_sum
#print axioms guba23_disjoint_dart_arcs_weight
#print axioms guba23_dart_boundary_transfer
#print axioms guba23_perimeter_arithmetic_six
#print axioms guba23_marked_boundary_transfer_darts


open SmallPresentationStatements.PermutationCycles

/-! ## Ordered paths between consecutive coefficient outlets

The first-return permutation from the pinned geometry library keeps
the genuine face cycles of the coefficient ribbon. In contrast to a
list of component representatives it records the intervening paths
with their actual incidence order.

These are face walks, not yet the short connecting paths of a Guba
contiguity subdiagram. Their disjointness is a statement about
departing darts, not disjointness of the visited lower-rank cells.
-/

/-- Two first-return paths with a common departure must start at
the same retained incidence. The argument uses the minimality of
the return times and injectivity of the original permutation. -/
theorem firstReturn_paths_disjoint {D : Type} [Finite D]
    (sigma : Equiv.Perm D) (ret : D → Prop)
    (a b : {d : D // ret d}) (hne : a ≠ b) :
    ∀ d,
      d ∈ List.ofFn (fun k : Fin (FirstReturn.time sigma ret a) =>
        sigma^[k.val] a.val) →
      d ∈ List.ofFn (fun k : Fin (FirstReturn.time sigma ret b) =>
        sigma^[k.val] b.val) → False := by
  have cancel (u v : {d : D // ret d}) (i j : ℕ)
      (hj : j < FirstReturn.time sigma ret v) (hij : i ≤ j)
      (he : sigma^[i] u.val = sigma^[j] v.val) : u = v := by
    have hsum : i + (j-i) = j := by omega
    have he' : sigma^[i] u.val = sigma^[i] (sigma^[j-i] v.val) := by
      rw [← Function.iterate_add_apply,hsum]
      exact he
    have huv := (sigma.injective.iterate i) he'
    by_cases hz : j-i = 0
    · apply Subtype.ext
      simpa only [hz,Function.iterate_zero_apply] using huv
    · exact False.elim ((FirstReturn.no_early sigma ret v (j-i)
        (by omega) (by omega)) (huv ▸ u.property))
  intro d ha hb
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hb
  rcases le_total i.val j.val with h | h
  · exact hne (cancel a b i.val j.val j.isLt h (hi.trans hj.symm))
  · exact hne (cancel b a j.val i.val i.isLt h (hj.trans hi.symm)).symm

/-- Retained incidence paths have exactly one retained departure,
namely their start. In particular a path cannot silently cross
another selected outlet before arriving at its actual next outlet. -/
theorem firstReturn_retained_departure {D : Type} [Finite D]
    (sigma : Equiv.Perm D) (ret : D → Prop) (a : {d : D // ret d})
    (d : D)
    (hd : d ∈ List.ofFn (fun k : Fin (FirstReturn.time sigma ret a) =>
      sigma^[k.val] a.val)) (hr : ret d) : d = a.val := by
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
  have hz : i.val = 0 := by
    by_contra h
    exact FirstReturn.no_early sigma ret a i.val (by omega) i.isLt (hi.symm ▸ hr)
  simpa only [hz,Function.iterate_zero_apply] using hi.symm

/-- The original coefficient refinement determines a system of
actual, ordered, nonoverlapping face-walk departures. The endpoint
permutation preserves precisely the face cycles that meet outlets.
No connected-component-to-disc implication is used. -/
theorem coefficient_region_ordered_paths {D : Type} [Fintype D]
    (P : RibbonMap D) (keep : D → Prop)
    (hkeep : ∀ d, keep (P.rotation d) ↔ keep d) :
    let S := P.coefficientRegions keep hkeep
    let A := {d : D // ¬ keep d}
    ∃ (next : Equiv.Perm A) (paths : A → List D),
      (∀ a, paths a ≠ [] ∧ (paths a).Nodup ∧
        Walk S.face a.val (next a).val (paths a)) ∧
      (∀ a d, d ∈ paths a → ¬ keep d → d = a.val) ∧
      (∀ a b, a ≠ b → ∀ d, d ∈ paths a → d ∈ paths b → False) ∧
      (∀ a b, next.SameCycle a b ↔ S.face.SameCycle a.val b.val) := by
  classical
  intro S A
  let next : Equiv.Perm A := P.regionBoundary keep hkeep
  let paths : A → List D := fun a =>
    List.ofFn (fun k : Fin (FirstReturn.time S.face (fun d => ¬ keep d) a) =>
      S.face^[k.val] a.val)
  refine ⟨next,paths,?_,?_,?_,?_⟩
  · intro a
    refine ⟨?_,FirstReturn.path_nodup S.face _ a,FirstReturn.walk S.face _ a⟩
    intro h
    have hn := congrArg List.length h
    change (List.ofFn (fun k : Fin (FirstReturn.time S.face (fun d => ¬ keep d) a) =>
      S.face^[k.val] a.val)).length = 0 at hn
    rw [List.length_ofFn] at hn
    exact (Nat.ne_of_gt (FirstReturn.time_pos S.face _ a)) hn
  · intro a d hd hr
    exact firstReturn_retained_departure S.face (fun e => ¬ keep e) a d hd hr
  · intro a b hab d ha hb
    exact firstReturn_paths_disjoint S.face (fun e => ¬ keep e) a b hab d ha hb
  · intro a b
    exact P.regionBoundary_sameCycle_iff keep hkeep a b

#print axioms firstReturn_paths_disjoint
#print axioms firstReturn_retained_departure
#print axioms coefficient_region_ordered_paths



/-! ## Two-sided relations from actual interval components

The global interval refinement may have components with several
peripheral vertices. When a coefficient component is exhausted by
two distinct literal blocks, it yields the exact inverse-conjugacy
relation of those two blocks modulo the protected vertex relations.
There is no need to specify a sequence of cuts, or to independently
assume the interior relator condition in the refined component.
This is not a claim that a multi-outlet component is a corridor.
-/
theorem coefficient_two_block_relation {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
    (tau : Equiv.Perm D)
    (hE : P.EulerEquality) (href : SplitRefinement P.rotation tau)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hprotected : ∀ d, keep d →
      (P.withRotation tau).vertexBoundary d = P.vertexBoundary d)
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (hcomp : ∀ d e, (P.withRotation tau).SameComponent d e ↔
      (P.coefficientRegions keep hstep).SameComponent d e)
    (a b : D) (u v : List D)
    (ha : (P.withRotation tau).vertexBoundary a = a :: u)
    (hb : (P.withRotation tau).vertexBoundary b = b :: v)
    (hsep : b ∉ a :: u)
    (hab : (P.coefficientRegions keep hstep).SameComponent a b)
    (hcover : ∀ d, (P.coefficientRegions keep hstep).SameComponent a d →
      ¬ keep d → d ∈ a :: u ∨ d ∈ b :: v) :
    ∃ g : F, FreeGroup.mk ((a :: u).map read) * g *
      FreeGroup.mk ((b :: v).map read) * g⁻¹ ∈ N := by
  let Q := P.withRotation tau
  have hQE : Q.EulerEquality := P.splitRefinement_preserves_euler href hE
  have hne : ¬ Q.rotation.SameCycle a b := by
    intro h
    have hm := (Q.mem_vertexBoundary_iff a b).mpr h
    rw [show Q.vertexBoundary a = a :: u from ha] at hm
    exact hsep hm
  have hinside : ∀ d, Q.SameComponent a d → ¬ Q.rotation.SameCycle a d →
      ¬ Q.rotation.SameCycle b d →
      FreeGroup.mk ((Q.vertexBoundary d).map read) ∈ N := by
    intro d hd hda hdb
    have hk : keep d := by
      by_contra hn
      rcases hcover d ((hcomp a d).mp hd) hn with hm | hm
      · apply hda
        apply (Q.mem_vertexBoundary_iff a d).mp
        rw [show Q.vertexBoundary a = a :: u from ha]
        exact hm
      · apply hdb
        apply (Q.mem_vertexBoundary_iff b d).mp
        rw [show Q.vertexBoundary b = b :: v from hb]
        exact hm
    rw [show Q.vertexBoundary d = P.vertexBoundary d from hprotected d hk]
    exact hint d hk
  obtain ⟨g,hg⟩ := component_two_boundary_inverse_conjugacy Q read N
    hedge hQE a b ((hcomp a b).mpr hab) hne hinside
  rw [show Q.vertexBoundary a = a :: u from ha,
      show Q.vertexBoundary b = b :: v from hb] at hg
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective N g
  refine ⟨z,(QuotientGroup.eq_one_iff _).mp ?_⟩
  change QuotientGroup.mk' N
    (FreeGroup.mk ((a :: u).map read) * z *
      FreeGroup.mk ((b :: v).map read) * z⁻¹) = 1
  simpa only [map_mul,map_inv] using hg

#print axioms coefficient_two_block_relation



/-- A coefficient component with just one peripheral block has
trivial block reading in the lower quotient. This is the single
exceptional vertex form of the boundary theorem. -/
theorem coefficient_one_block_mem {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
    (tau : Equiv.Perm D)
    (hE : P.EulerEquality) (href : SplitRefinement P.rotation tau)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hprotected : ∀ d, keep d →
      (P.withRotation tau).vertexBoundary d = P.vertexBoundary d)
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (hcomp : ∀ d e, (P.withRotation tau).SameComponent d e ↔
      (P.coefficientRegions keep hstep).SameComponent d e)
    (a : D) (u : List D)
    (ha : (P.withRotation tau).vertexBoundary a = a :: u)
    (hcover : ∀ d, (P.coefficientRegions keep hstep).SameComponent a d →
      ¬ keep d → d ∈ a :: u) :
    FreeGroup.mk ((a :: u).map read) ∈ N := by
  let Q := P.withRotation tau
  have hm := component_boundary_mem_normal Q read N hedge
    (P.splitRefinement_preserves_euler href hE) a (by
      intro d hd hne
      have hk : keep d := by
        by_contra hn
        apply hne
        apply (Q.mem_vertexBoundary_iff a d).mp
        rw [show Q.vertexBoundary a = a :: u from ha]
        exact hcover d ((hcomp a d).mp hd) hn
      rw [show Q.vertexBoundary d = P.vertexBoundary d from hprotected d hk]
      exact hint d hk)
  rw [show Q.vertexBoundary a = a :: u from ha] at hm
  exact hm

/-- A positive-weight literal factor of a minimal bad period
cannot be trivial in its preceding quotient. Compare with the
empty replacement word using the already proved minimality lemma. -/
theorem minBad_positive_factor_not_mem {N : Subgroup F} [N.Normal]
    {c : F} (hc : MinBad N c) (p v r : RawWord)
    (hword : c.toWord = p ++ v ++ r) (hv : 0 < rawWeight v) :
    FreeGroup.mk v ∉ N := by
  intro hm
  have he : QuotientGroup.mk' N (FreeGroup.mk v) =
      QuotientGroup.mk' N (FreeGroup.mk ([] : RawWord)) := by
    rw [← FreeGroup.one_eq_mk, map_one]
    exact (QuotientGroup.eq_one_iff _).mpr hm
  have hz := minBad_factor_weight_min hc p v r [] hword he
  change rawWeight v ≤ 0 at hz
  omega

/-- A genuine minimal-period block of positive weight cannot
exhaust all peripheral incidences of its coefficient component.
There must be a second outlet outside the block, not merely a
second dart within the same block. -/
theorem coefficient_minBad_block_has_other_outlet {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (keep : D → Prop) (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
    (tau : Equiv.Perm D)
    (hE : P.EulerEquality) (href : SplitRefinement P.rotation tau)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hprotected : ∀ d, keep d →
      (P.withRotation tau).vertexBoundary d = P.vertexBoundary d)
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (hcomp : ∀ d e, (P.withRotation tau).SameComponent d e ↔
      (P.coefficientRegions keep hstep).SameComponent d e)
    (a : D) (u : List D)
    (ha : (P.withRotation tau).vertexBoundary a = a :: u)
    {c : F} (hc : MinBad N c) (p r : RawWord)
    (hword : c.toWord = p ++ (a :: u).map read ++ r)
    (hw : 0 < rawWeight ((a :: u).map read)) :
    ∃ d, (P.coefficientRegions keep hstep).SameComponent a d ∧
      ¬ keep d ∧ d ∉ a :: u := by
  classical
  by_contra hn
  apply minBad_positive_factor_not_mem hc p ((a :: u).map read) r hword hw
  apply coefficient_one_block_mem P read N keep hstep tau hE href
    hedge hprotected hint hcomp a u ha
  intro d hd hk
  by_contra hm
  exact hn ⟨d,hd,hk,hm⟩

#print axioms coefficient_one_block_mem
#print axioms minBad_positive_factor_not_mem
#print axioms coefficient_minBad_block_has_other_outlet


end QuandleResearch.Issue070
