import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy
import Mathlib.Basic.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.FinRange
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



/-! ## Metric information supplied by a two-sided quotient relation

The algebraic boundary theorem alone does not give short connectors:
conjugacy can have an arbitrarily long witness. Retain its actual
weighted length in the replacement estimate rather than treating
conjugacy as equality or silently ignoring that length.
-/

/-- A literal factor of a minimal bad period can be replaced by the
inverse of the opposite reading conjugated by the actual witness. -/
theorem minBad_factor_inverse_conjugacy_weight {N : Subgroup F} [N.Normal]
    {c : F} (hc : MinBad N c) (p u r v : RawWord) (g : F)
    (hword : c.toWord = p ++ u ++ r)
    (hrel : FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N) :
    rawWeight u ≤ rawWeight v + 2 * weightedLength g := by
  let q := QuotientGroup.mk' N
  have he : q (FreeGroup.mk u) * q g * q (FreeGroup.mk v) * (q g)⁻¹ = 1 := by
    have h : q (FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hrel
    simpa only [map_mul,map_inv] using h
  have hq : q (FreeGroup.mk u) =
      q (FreeGroup.mk (g.toWord ++ FreeGroup.invRev v ++
        FreeGroup.invRev g.toWord)) := by
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, FreeGroup.mk_toWord,
      map_mul, map_inv]
    calc
      q (FreeGroup.mk u) =
          (q (FreeGroup.mk u) * q g * q (FreeGroup.mk v) * (q g)⁻¹) *
            (q g * (q (FreeGroup.mk v))⁻¹ * (q g)⁻¹) := by group
      _ = _ := by rw [he,one_mul]
  have hmin := minBad_factor_weight_min hc p u r
    (g.toWord ++ FreeGroup.invRev v ++ FreeGroup.invRev g.toWord) hword hq
  rw [rawWeight_append,rawWeight_append,rawWeight_invRev,rawWeight_invRev] at hmin
  change rawWeight u ≤ rawWeight v + 2 * rawWeight g.toWord
  -- Both occurrences of the conjugator are charged with their literal weights.
  omega

/-- Minimize the actual weighted conjugating word among witnesses
of the two-block relation. This introduces no new axiom or claim
that a short geometric bond exists. -/
theorem exists_minimal_inverse_conjugator_weight (N : Subgroup F)
    (u v : RawWord)
    (hex : ∃ g : F, FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N) :
    ∃ g : F, FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N ∧
      ∀ h : F, FreeGroup.mk u * h * FreeGroup.mk v * h⁻¹ ∈ N →
        weightedLength g ≤ weightedLength h := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ g : F, FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N ∧
      weightedLength g = n
  have hP : ∃ n, P n := by
    obtain ⟨g,hg⟩ := hex
    exact ⟨weightedLength g,g,hg,rfl⟩
  obtain ⟨g,hg,hw⟩ := Nat.find_spec hP
  refine ⟨g,hg,?_⟩
  intro h hh
  rw [hw]
  exact Nat.find_min' hP ⟨h,hh,rfl⟩

#print axioms minBad_factor_inverse_conjugacy_weight
#print axioms exists_minimal_inverse_conjugator_weight



/-! ## Explicit connector readings at an actual edge splice

The earlier two-boundary theorem discards the length of the
conjugator when it changes base corners. Retain the literal
departure words instead. The following local splice estimate
charges exactly their weights, without any claim yet that a
preferred system of short connectors exists.
-/

/-- Change of base corner along an actual walk, with its explicit
ordered conjugating product rather than an existential witness. -/
theorem walk_cycleProduct_transport {D K : Type} [Finite D] [Group K]
    (sigma : Equiv.Perm D) (v : D → K)
    {a b : D} {l : List D} (h : Walk sigma a b l) :
    cycleProduct sigma v a * (l.map v).prod =
      (l.map v).prod * cycleProduct sigma v b := by
  induction h with
  | nil d => simp
  | cons d e l ht ih =>
    obtain ⟨tail, htail⟩ := cycleBoundary_cons sigma d
    have hnext : cycleProduct sigma v (sigma d) =
        (v d)⁻¹ * cycleProduct sigma v d * v d := by
      simp only [cycleProduct, cycleBoundary_next sigma d tail htail, htail,
        List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      group
    simp only [List.map_cons,List.prod_cons]
    calc
      _ = v d * (cycleProduct sigma v (sigma d) * (l.map v).prod) := by
        rw [hnext]
        group
      _ = _ := by rw [ih]; group

/-- The actual connector words are obtained from the two rotation
walks to the corners selected by the edge splice. Their combined
weight bounds the conjugator in the lower quotient. -/
theorem edgeSplice_explicit_inverse_conjugator {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (c : D) (hn : ¬ P.rotation.SameCycle c (P.edge c))
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, P.SameComponent c d →
      ¬ P.rotation.SameCycle c d →
      ¬ P.rotation.SameCycle (P.edge c) d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a b : D) (p r : List D)
    (hp : Walk P.rotation a (P.rotation c) p)
    (hr : Walk P.rotation b (P.edge c) r) :
    let g := FreeGroup.mk (p.map read ++ FreeGroup.invRev (r.map read))
    FreeGroup.mk ((P.vertexBoundary a).map read) * g *
      FreeGroup.mk ((P.vertexBoundary b).map read) * g⁻¹ ∈ N ∧
      weightedLength g ≤ rawWeight (p.map read) + rawWeight (r.map read) := by
  let q := QuotientGroup.mk' N
  let val : D → F ⧸ N := fun d => q (FreeGroup.mk [read d])
  have eval (ds : List D) :
      (ds.map val).prod = q (FreeGroup.mk (ds.map read)) := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons d ds ih =>
      change val d * (ds.map val).prod =
        q (FreeGroup.mk ([read d] ++ ds.map read))
      rw [ih, ← FreeGroup.mul_mk, map_mul]
  have based (d : D) : cycleProduct P.rotation val d =
      q (FreeGroup.mk ((P.vertexBoundary d).map read)) :=
    eval (P.vertexBoundary d)
  have hA := walk_cycleProduct_transport P.rotation val hp
  have hB := walk_cycleProduct_transport P.rotation val hr
  simp only [based, eval] at hA hB
  have hm := edgeSplice_boundary_mem_normal P read N c hn hE he hint
  have hm' : q (FreeGroup.mk (((P.vertexBoundary (P.rotation c)).map read) ++
      (P.vertexBoundary (P.edge c)).map read)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hm
  rw [← FreeGroup.mul_mk, map_mul] at hm'
  dsimp only
  constructor
  · apply (QuotientGroup.eq_one_iff _).mp
    change q (FreeGroup.mk ((P.vertexBoundary a).map read) *
      FreeGroup.mk (p.map read ++ FreeGroup.invRev (r.map read)) *
      FreeGroup.mk ((P.vertexBoundary b).map read) *
      (FreeGroup.mk (p.map read ++ FreeGroup.invRev (r.map read)))⁻¹) = 1
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv]
    have ha : q (FreeGroup.mk ((P.vertexBoundary a).map read)) =
        q (FreeGroup.mk (p.map read)) *
          q (FreeGroup.mk ((P.vertexBoundary (P.rotation c)).map read)) *
          (q (FreeGroup.mk (p.map read)))⁻¹ := by
      calc
        _ = (q (FreeGroup.mk ((P.vertexBoundary a).map read)) *
              q (FreeGroup.mk (p.map read))) *
              (q (FreeGroup.mk (p.map read)))⁻¹ := by group
        _ = _ := by rw [hA]
    have hb : q (FreeGroup.mk ((P.vertexBoundary b).map read)) =
        q (FreeGroup.mk (r.map read)) *
          q (FreeGroup.mk ((P.vertexBoundary (P.edge c)).map read)) *
          (q (FreeGroup.mk (r.map read)))⁻¹ := by
      calc
        _ = (q (FreeGroup.mk ((P.vertexBoundary b).map read)) *
              q (FreeGroup.mk (r.map read))) *
              (q (FreeGroup.mk (r.map read)))⁻¹ := by group
        _ = _ := by rw [hB]
    rw [ha,hb]
    calc
      _ = q (FreeGroup.mk (p.map read)) *
        (q (FreeGroup.mk ((P.vertexBoundary (P.rotation c)).map read)) *
          q (FreeGroup.mk ((P.vertexBoundary (P.edge c)).map read))) *
          (q (FreeGroup.mk (p.map read)))⁻¹ := by group
      _ = 1 := by rw [hm']; simp
  · have h := weightedLength_mk_le (p.map read ++ FreeGroup.invRev (r.map read))
    rwa [rawWeight_append,rawWeight_invRev] at h

#print axioms walk_cycleProduct_transport
#print axioms edgeSplice_explicit_inverse_conjugator



/-! ## Absorbing trivial vertices without changing the marked base

An interior vertex whose cycle product is one can be absorbed into
the first marked vertex without conjugating the product at its
original marked corner. Thus successive absorptions need not pay
for repeated changes of base along the growing merged cycle.
The reduction below leaves two adjacent exceptional vertices, with
both original based products exactly preserved. It is topological
and algebraic; it does not bound the metric length of the eventual
connector by Guba's small fraction of a perimeter.
-/

/-- Inserting a trivial cycle into another cycle preserves the
product at every old corner of the latter. -/
theorem cycleProduct_cutAt_trivial_insert {D K : Type} [Finite D] [Group K]
    (sigma : Equiv.Perm D) (v : D → K) (x y a : D)
    (hxy : ¬ sigma.SameCycle x y)
    (hxa : sigma.SameCycle x a)
    (hy : cycleProduct sigma v y = 1) :
    cycleProduct (cutAt sigma x y) v a = cycleProduct sigma v a := by
  let k := (orbitEquiv sigma x).symm ⟨a,hxa⟩
  have hka : sigma^[k.val] x = a := by
    have hk : (orbitEquiv sigma x k).val = a :=
      congrArg Subtype.val ((orbitEquiv sigma x).apply_symm_apply ⟨a,hxa⟩)
    rw [orbitEquiv_val] at hk
    simpa only [Equiv.Perm.coe_pow] using hk
  let l := List.ofFn (fun i : Fin k.val => sigma^[i.val] x)
  have hw : Walk sigma x a l := by
    rw [← hka]
    exact Walk.of_iterate sigma k.val x
  have hka' : (cutAt sigma x y)^[k.val] x = a :=
    (cutAt_iterate_before_return sigma x y hxy k.val k.isLt).trans hka
  have hl : List.ofFn (fun i : Fin k.val => (cutAt sigma x y)^[i.val] x) = l := by
    apply congrArg List.ofFn
    funext i
    exact cutAt_iterate_before_return sigma x y hxy i.val (i.isLt.trans k.isLt)
  have hw' : Walk (cutAt sigma x y) x a l := by
    have h := Walk.of_iterate (cutAt sigma x y) k.val x
    rwa [hka',hl] at h
  have hs := walk_cycleProduct_transport sigma v hw
  have ht := walk_cycleProduct_transport (cutAt sigma x y) v hw'
  rw [cycleProduct_cutAt_merge sigma v x y hxy,hy,mul_one] at ht
  exact mul_left_cancel (ht.symm.trans hs)

/-- A connected spherical ribbon with two exceptional vertices
can be changed by absorbing only trivial vertices until an actual
edge joins the marked cycles. All darts, the edge permutation,
and the two original based products are retained. -/
theorem two_boundary_adjacent_reduction {D K : Type} [Fintype D] [Group K]
    (P : RibbonMap D) (v : D → K)
    (hc : P.Connected) (hE : P.EulerEquality)
    (a b : D) (hab : ¬ P.rotation.SameCycle a b)
    (hint : ∀ d, ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d → cycleProduct P.rotation v d = 1) :
    ∃ Q : RibbonMap D, Q.Connected ∧ Q.EulerEquality ∧ Q.edge = P.edge ∧
      cycleProduct Q.rotation v a = cycleProduct P.rotation v a ∧
      cycleProduct Q.rotation v b = cycleProduct P.rotation v b ∧
      (∀ d, ¬ Q.rotation.SameCycle a d →
        ¬ Q.rotation.SameCycle b d → cycleProduct Q.rotation v d = 1) ∧
      ¬ Q.rotation.SameCycle a b ∧
      ∃ c, Q.rotation.SameCycle a c ∧ Q.rotation.SameCycle b (Q.edge c) := by
  classical
  obtain ⟨c,hac,hce⟩ := guba22_exists_leaving_edge P hc a b hab
  by_cases hb : P.rotation.SameCycle b (P.edge c)
  · exact ⟨P,hc,hE,rfl,rfl,rfl,hint,hab,c,hac,hb⟩
  · have hn : ¬ P.rotation.SameCycle c (P.edge c) :=
      fun h => hce (hac.trans h)
    have hnc : ¬ P.rotation.SameCycle (P.rotation c) (P.edge c) := by
      simpa only [Equiv.Perm.sameCycle_apply_left] using hn
    let S := P.edgeSplice c
    have hES : S.EulerEquality := (P.edgeSplice_euler_iff c hn).mpr hE
    have hCS : S.Connected := guba22_edgeSplice_connected P hc c hn
    have hca : P.rotation.SameCycle a (P.rotation c) :=
      hac.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    have hzero : cycleProduct P.rotation v (P.edge c) = 1 :=
      hint _ hce hb
    have haS : cycleProduct S.rotation v a = cycleProduct P.rotation v a :=
      cycleProduct_cutAt_trivial_insert P.rotation v (P.rotation c) (P.edge c)
        a hnc hca.symm hzero
    have hbS : cycleProduct S.rotation v b = cycleProduct P.rotation v b :=
      cycleProduct_cutAt_unchanged P.rotation v _ _ _ (fun h => hab (hca.trans h.symm)) hb
    have habS : ¬ S.rotation.SameCycle a b := by
      intro h
      rcases (P.edgeSplice_sameVertex_iff c hn a b).mp h with h | h
      · exact hab h
      · rcases h.2 with h' | h'
        · exact hab (hac.trans h'.symm)
        · exact hb h'
    have hintS : ∀ d, ¬ S.rotation.SameCycle a d →
        ¬ S.rotation.SameCycle b d → cycleProduct S.rotation v d = 1 := by
      intro d hd hbd
      have hda : ¬ P.rotation.SameCycle d (P.rotation c) := by
        intro h
        exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc (hca.trans h.symm))
      have hde : ¬ P.rotation.SameCycle d (P.edge c) := by
        intro h
        have hx : S.rotation.SameCycle (P.rotation c) (P.edge c) :=
          cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc
        exact hd ((sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc hca).trans
          (hx.trans (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h.symm)))
      change cycleProduct (cutAt P.rotation (P.rotation c) (P.edge c)) v d = 1
      rw [cycleProduct_cutAt_unchanged P.rotation v _ _ _ hda hde]
      apply hint d
      · intro h
        exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h)
      · intro h
        exact hbd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h)
    obtain ⟨Q,hQC,hQE,hQedge,hQa,hQb,hQi,hQab,z,hza,hzb⟩ :=
      two_boundary_adjacent_reduction S v hCS hES a b habS hintS
    refine ⟨Q,hQC,hQE,?_,hQa.trans haS,hQb.trans hbS,hQi,hQab,z,hza,hzb⟩
    exact hQedge
termination_by Fintype.card P.Vertex
decreasing_by
  have hcount := (P.edgeSplice_counts c hn).1
  change Fintype.card (P.edgeSplice c).Vertex < Fintype.card P.Vertex
  omega

#print axioms cycleProduct_cutAt_trivial_insert
#print axioms two_boundary_adjacent_reduction



/-! ## Shorter of the two boundary routes

A change of marked corner can use either complementary part of
the complete cycle. The backward route is read with inverse
orientation; it is not a forward walk with the same labels.
The resulting factor of one half is valid for arbitrary positive
letter weights, but by itself is not the small-cancellation
constant required of a preferred bond.
-/

/-- Split the actual cycle into complementary walks from a to b
and from b back to a. Empty first walks are allowed. -/
theorem vertex_two_complementary_walks {D : Type} [Fintype D]
    (P : RibbonMap D) (a b : D) (hab : P.rotation.SameCycle a b) :
    ∃ p r : List D, P.vertexBoundary a = p ++ r ∧
      Walk P.rotation a b p ∧ Walk P.rotation b a r := by
  have hm := (P.mem_vertexBoundary_iff a b).mpr hab
  obtain ⟨p,r,he⟩ := List.mem_iff_append.mp hm
  have hw : Walk P.rotation a a (P.vertexBoundary a) :=
    cycleBoundary_walk _ _
  rw [he] at hw
  obtain ⟨d,hp,hr⟩ := walk_split_departures P.rotation p (b :: r) a a hw
  have hd : d = b := by
    cases hr
    rfl
  subst d
  exact ⟨p,b :: r,he,hp,hr⟩

/-- A corner change admits a literal connector word of weight at
most half of the entire cycle. The two transport identities follow
from the complementary actual walks and inversion, without assuming
the cycle product is trivial. -/
theorem vertex_short_corner_connector {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a b : D)
    (hab : P.rotation.SameCycle a b) :
    ∃ u : RawWord,
      FreeGroup.mk ((P.vertexBoundary a).map read) * FreeGroup.mk u =
        FreeGroup.mk u * FreeGroup.mk ((P.vertexBoundary b).map read) ∧
      2 * rawWeight u ≤ rawWeight ((P.vertexBoundary a).map read) := by
  obtain ⟨p,r,hpart,hp,hr⟩ := vertex_two_complementary_walks P a b hab
  let v : D → F := fun d => FreeGroup.mk [read d]
  have eval (l : List D) : (l.map v).prod = FreeGroup.mk (l.map read) := by
    induction l with
    | nil => rfl
    | cons d ds ih =>
      change v d * (ds.map v).prod = FreeGroup.mk ([read d] ++ ds.map read)
      rw [ih,← FreeGroup.mul_mk]
  have based (d : D) : cycleProduct P.rotation v d =
      FreeGroup.mk ((P.vertexBoundary d).map read) := eval (P.vertexBoundary d)
  have hforward := walk_cycleProduct_transport P.rotation v hp
  have hbackward := walk_cycleProduct_transport P.rotation v hr
  simp only [based,eval] at hforward hbackward
  have hweight : rawWeight ((P.vertexBoundary a).map read) =
      rawWeight (p.map read) + rawWeight (r.map read) := by
    rw [hpart,List.map_append,rawWeight_append]
  rcases le_total (rawWeight (p.map read)) (rawWeight (r.map read)) with h | h
  · exact ⟨p.map read,hforward,by omega⟩
  · refine ⟨FreeGroup.invRev (r.map read),?_,?_⟩
    · rw [← FreeGroup.inv_mk]
      calc
        _ = (FreeGroup.mk (r.map read))⁻¹ *
            (FreeGroup.mk (r.map read) * FreeGroup.mk ((P.vertexBoundary a).map read)) *
            (FreeGroup.mk (r.map read))⁻¹ := by group
        _ = _ := by rw [← hbackward]; group
    · rw [rawWeight_invRev]
      omega

#print axioms vertex_two_complementary_walks
#print axioms vertex_short_corner_connector



/-! ## Guba Lemma 1: numerical closing step of the bond induction

Source: V. S. Guba, A finitely generated complete group, Math. USSR
Izv. 29 (1987), pp. 243--244. The principal-cell perimeter and
connector budgets alone are insufficient: the estimate on q uses
the lower-rank periodic compatibility theorem (Lemma 39, via
Lemma 2), and the transfer estimate uses Lemma 21. Both are
explicit premises here. This is not the existence of a bond.
-/

/-- If a principal-cell bond has the local degree, transfer,
periodic-overlap and connector bounds in Lemma 1, the desired
4 T beta^{-1} bound follows with the original constants. -/
theorem guba1_bond_connector_arithmetic (P L t q s1 s2 C b : ℚ)
    (hC : 0 < C)
    (hP : P ≤ 3*10^11*L)
    (hdegree : (1/10^17 : ℚ)*L ≤ t)
    (htransfer : (9/10 : ℚ)*t ≤ s1+s2+q)
    (hshort : s1+s2 ≤ 2*(1/10^19 : ℚ)*t)
    (hoverlap : q ≤ (1+1/120 : ℚ)*C)
    (hb : b ≤ (1+2*(1/10^19 : ℚ))*P) :
    b < 4*10^28*C := by
  norm_num at hP hdegree htransfer hshort hoverlap hb ⊢
  linarith only [hC,hP,hdegree,htransfer,hshort,hoverlap,hb]

/-- The local long-section corollary follows once the actual
period-to-section size comparison is established. No diagram
existence or periodicity assumption is discharged by arithmetic. -/
theorem guba1_long_section_connector_arithmetic (C L b : ℚ)
    (hb : b < 4*10^28*C)
    (hscale : 4*10^28*C ≤ (1/10^19 : ℚ)*L) :
    b < (1/10^19 : ℚ)*L :=
  lt_of_lt_of_le hb hscale

#print axioms guba1_bond_connector_arithmetic
#print axioms guba1_long_section_connector_arithmetic



/-! ## Weighted conjugator across adjacent exceptional vertices

Use the shorter of the two literal boundary routes at each marked
corner. Unlike the unrestricted walk version, the connector has a
bound in terms of the two actual vertex perimeters. This does not
assert that a preferred Guba bond exists or has the required small
relative perimeter.
-/

theorem adjacent_short_inverse_conjugator {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (c : D) (hn : ¬ P.rotation.SameCycle c (P.edge c))
    (hE : P.EulerEquality)
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, P.SameComponent c d →
      ¬ P.rotation.SameCycle c d →
      ¬ P.rotation.SameCycle (P.edge c) d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (a b : D)
    (ha : P.rotation.SameCycle a (P.rotation c))
    (hb : P.rotation.SameCycle b (P.edge c)) :
    ∃ g : F, FreeGroup.mk ((P.vertexBoundary a).map read) * g *
      FreeGroup.mk ((P.vertexBoundary b).map read) * g⁻¹ ∈ N ∧
      2 * weightedLength g ≤ rawWeight ((P.vertexBoundary a).map read) +
        rawWeight ((P.vertexBoundary b).map read) := by
  obtain ⟨u,hu,hwu⟩ := vertex_short_corner_connector P read a (P.rotation c) ha
  obtain ⟨v,hv,hwv⟩ := vertex_short_corner_connector P read b (P.edge c) hb
  let q := QuotientGroup.mk' N
  have hU := congrArg (fun x : F => q x) hu
  have hV := congrArg (fun x : F => q x) hv
  simp only [map_mul] at hU hV
  have hm := edgeSplice_boundary_mem_normal P read N c hn hE he hint
  have hm' : q (FreeGroup.mk (((P.vertexBoundary (P.rotation c)).map read) ++
      (P.vertexBoundary (P.edge c)).map read)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hm
  rw [← FreeGroup.mul_mk, map_mul] at hm'
  have hA : q (FreeGroup.mk ((P.vertexBoundary a).map read)) =
      q (FreeGroup.mk u) *
        q (FreeGroup.mk ((P.vertexBoundary (P.rotation c)).map read)) *
        (q (FreeGroup.mk u))⁻¹ := by
    calc
      _ = (q (FreeGroup.mk ((P.vertexBoundary a).map read)) *
            q (FreeGroup.mk u)) * (q (FreeGroup.mk u))⁻¹ := by group
      _ = _ := by rw [hU]
  have hB : q (FreeGroup.mk ((P.vertexBoundary b).map read)) =
      q (FreeGroup.mk v) *
        q (FreeGroup.mk ((P.vertexBoundary (P.edge c)).map read)) *
        (q (FreeGroup.mk v))⁻¹ := by
    calc
      _ = (q (FreeGroup.mk ((P.vertexBoundary b).map read)) *
            q (FreeGroup.mk v)) * (q (FreeGroup.mk v))⁻¹ := by group
      _ = _ := by rw [hV]
  refine ⟨FreeGroup.mk (u ++ FreeGroup.invRev v), ?_, ?_⟩
  · apply (QuotientGroup.eq_one_iff _).mp
    change q (FreeGroup.mk ((P.vertexBoundary a).map read) *
      FreeGroup.mk (u ++ FreeGroup.invRev v) *
      FreeGroup.mk ((P.vertexBoundary b).map read) *
      (FreeGroup.mk (u ++ FreeGroup.invRev v))⁻¹) = 1
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv]
    rw [hA,hB]
    calc
      _ = q (FreeGroup.mk u) *
        (q (FreeGroup.mk ((P.vertexBoundary (P.rotation c)).map read)) *
          q (FreeGroup.mk ((P.vertexBoundary (P.edge c)).map read))) *
        (q (FreeGroup.mk u))⁻¹ := by group
      _ = 1 := by rw [hm']; simp
  · have hg := weightedLength_mk_le (u ++ FreeGroup.invRev v)
    rw [rawWeight_append, rawWeight_invRev] at hg
    omega

#print axioms adjacent_short_inverse_conjugator



/-! ## A global metric version of the two-exceptional-vertex lemma

The earlier absorption procedure preserves all original darts and the
two based products. Consequently the two final perimeters are bounded
by the original total dart weight. This gives a metric estimate without
paying separately for every absorption.
-/

/-- The perimeters of two distinct vertices count disjoint sets of
darts, so their sum is at most the total dart weight. -/
theorem two_vertex_perimeters_le_total {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a b : D)
    (hab : ¬ P.rotation.SameCycle a b) :
    rawWeight ((P.vertexBoundary a).map read) +
      rawWeight ((P.vertexBoundary b).map read) ≤
      ∑ d : D, letterWeight (read d) := by
  classical
  have hd : Disjoint (P.vertexBoundary a).toFinset
      (P.vertexBoundary b).toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hda hdb
    exact hab (((P.mem_vertexBoundary_iff a d).mp (List.mem_toFinset.mp hda)).trans
      ((P.mem_vertexBoundary_iff b d).mp (List.mem_toFinset.mp hdb)).symm)
  rw [dart_read_weight_sum read _ (P.vertexBoundary_nodup a),
      dart_read_weight_sum read _ (P.vertexBoundary_nodup b),
      ← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _)

/-- Two exceptional vertex words in a connected spherical diagram
are inverse-conjugate modulo its other vertex words by a conjugator
of at most half the total dart weight. No adjacency hypothesis is
needed. The much stronger relative estimate of Guba's preferred
bond still requires graded-diagram arguments. -/
theorem two_boundary_weighted_inverse_conjugator {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hc : P.Connected) (hE : P.EulerEquality)
    (a b : D) (hab : ¬ P.rotation.SameCycle a b)
    (hint : ∀ d, ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N) :
    ∃ g : F, FreeGroup.mk ((P.vertexBoundary a).map read) * g *
      FreeGroup.mk ((P.vertexBoundary b).map read) * g⁻¹ ∈ N ∧
      2 * weightedLength g ≤ ∑ d : D, letterWeight (read d) := by
  classical
  let q := QuotientGroup.mk' N
  let v : D → F ⧸ N := fun d => q (FreeGroup.mk [read d])
  have eval (ds : List D) :
      (ds.map v).prod = q (FreeGroup.mk (ds.map read)) := by
    induction ds with
    | nil => simp [← FreeGroup.one_eq_mk]
    | cons d ds ih =>
      change v d * (ds.map v).prod =
        q (FreeGroup.mk ([read d] ++ ds.map read))
      rw [ih, ← FreeGroup.mul_mk, map_mul]
  have based (S : RibbonMap D) (d : D) :
      cycleProduct S.rotation v d =
        q (FreeGroup.mk ((S.vertexBoundary d).map read)) :=
    eval (S.vertexBoundary d)
  have hinside : ∀ d, ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d → cycleProduct P.rotation v d = 1 := by
    intro d ha hb
    rw [based]
    exact (QuotientGroup.eq_one_iff _).mpr (hint d ha hb)
  obtain ⟨Q,hQC,hQE,hQedge,hQa,hQb,hQi,hQab,c,hca,hcb⟩ :=
    two_boundary_adjacent_reduction P v hc hE a b hab hinside
  have hcn : ¬ Q.rotation.SameCycle c (Q.edge c) :=
    fun h => hQab (hca.trans (h.trans hcb.symm))
  have hcar : Q.rotation.SameCycle a (Q.rotation c) :=
    hca.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  have hQe : ∀ d, read (Q.edge d) = reverseLetter (read d) := by
    intro d
    rw [hQedge]
    exact he d
  have hQin : ∀ d, Q.SameComponent c d →
      ¬ Q.rotation.SameCycle c d →
      ¬ Q.rotation.SameCycle (Q.edge c) d →
      FreeGroup.mk ((Q.vertexBoundary d).map read) ∈ N := by
    intro d _ hd hd'
    apply (QuotientGroup.eq_one_iff _).mp
    change q (FreeGroup.mk ((Q.vertexBoundary d).map read)) = 1
    rw [← based]
    exact hQi d (fun h => hd (hca.symm.trans h))
      (fun h => hd' (hcb.symm.trans h))
  obtain ⟨g,hg,hw⟩ := adjacent_short_inverse_conjugator Q read N c hcn
    hQE hQe hQin a b hcar hcb
  have hA := hQa
  have hB := hQb
  simp only [based] at hA hB
  refine ⟨g,?_,hw.trans (two_vertex_perimeters_le_total Q read a b hQab)⟩
  apply (QuotientGroup.eq_one_iff _).mp
  have h := (QuotientGroup.eq_one_iff _).mpr hg
  change q (FreeGroup.mk ((Q.vertexBoundary a).map read) * g *
      FreeGroup.mk ((Q.vertexBoundary b).map read) * g⁻¹) = 1 at h
  change q (FreeGroup.mk ((P.vertexBoundary a).map read) * g *
      FreeGroup.mk ((P.vertexBoundary b).map read) * g⁻¹) = 1
  simp only [map_mul,map_inv] at h ⊢
  rw [hA,hB] at h
  exact h

#print axioms two_vertex_perimeters_le_total
#print axioms two_boundary_weighted_inverse_conjugator



/-! ## Local metric estimate for a protected two-arc region

Restrict the weighted conjugator theorem to the actual component
of the refinement. Other components, including all their lower-rank
cells, contribute nothing to its length bound.
-/

attribute [local instance] Classical.propDecidable

theorem component_weighted_inverse_conjugator {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (he : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hE : P.EulerEquality) (a b : D)
    (hab : P.SameComponent a b) (hne : ¬ P.rotation.SameCycle a b)
    (hint : ∀ d, P.SameComponent a d → ¬ P.rotation.SameCycle a d →
      ¬ P.rotation.SameCycle b d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N) :
    ∃ g : F, FreeGroup.mk ((P.vertexBoundary a).map read) * g *
      FreeGroup.mk ((P.vertexBoundary b).map read) * g⁻¹ ∈ N ∧
      2 * weightedLength g ≤
        ∑ d : {d : D // P.SameComponent a d}, letterWeight (read d.val) := by
  classical
  let C := P.componentRibbon a
  let x : {d : D // P.SameComponent a d} := ⟨a,Relation.EqvGen.refl a⟩
  let y : {d : D // P.SameComponent a d} := ⟨b,hab⟩
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
  have hCe : ∀ d, read (C.edge d).val = reverseLetter (read d.val) := by
    intro d
    change read (P.edge d.val) = reverseLetter (read d.val)
    exact he d.val
  have hCi : ∀ d, ¬ C.rotation.SameCycle x d →
      ¬ C.rotation.SameCycle y d →
      FreeGroup.mk ((C.vertexBoundary d).map (fun e => read e.val)) ∈ N := by
    intro d hdx hdy
    rw [component_vertex_read P read a d]
    apply hint d.val d.property
    · intro h
      exact hdx ((P.restrict_sameVertex_iff (P.SameComponent a)
        (P.component_membership_edge a) (P.component_membership_rotation a) x d).mpr h)
    · intro h
      exact hdy ((P.restrict_sameVertex_iff (P.SameComponent a)
        (P.component_membership_edge a) (P.component_membership_rotation a) y d).mpr h)
  obtain ⟨g,hg,hw⟩ := two_boundary_weighted_inverse_conjugator C
    (fun d => read d.val) N hCe (P.componentRibbon_connected a) hEC x y hxy hCi
  rw [component_vertex_read P read a x, component_vertex_read P read a y] at hg
  exact ⟨g,hg,hw⟩

#print axioms component_weighted_inverse_conjugator


/-- The protected rank-ribbon refinement now supplies a quantitative
conjugator whose budget counts only its actual two-arc component. -/
theorem rankRibbon_protected_two_arc_weighted_conjugacy (pick : WeightedSelector)
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
          weightedHeightStage pick X j ∧
        2 * weightedLength g ≤
          ∑ d : {d // (P.withRotation S.rotation).SameComponent a d},
            letterWeight (read d.val) := by
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
  exact component_weighted_inverse_conjugator T read N he hET a b hab hne hinside

#print axioms rankRibbon_protected_two_arc_weighted_conjugacy



/-! ## Two-sided local transfer across a conjugating corridor

Minimality applies to a factor of any cyclic rotation of either
period. The two periods need not be selected at the same rank:
a relation at the earlier stage remains valid at the later stage.
This is the algebraic transfer estimate for short factors (within
one period), not the long periodic-overlap theorem.
-/

theorem minBad_cyclicFactor_inverse_conjugacy_weight
    {N : Subgroup F} [N.Normal] {c : F} (hc : MinBad N c)
    (l r p u s v : RawWord) (g : F)
    (hword : c.toWord = l ++ r)
    (hfactor : r ++ l = p ++ u ++ s)
    (hrel : FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N) :
    rawWeight u ≤ rawWeight v + 2 * weightedLength g :=
  minBad_factor_inverse_conjugacy_weight (minBad_rotation hc l r hword).1
    p u s v g ((minBad_rotation_toWord hc l r hword).trans hfactor) hrel

/-- In a corridor between two cyclic period factors, the loss in
either direction is at most twice the weight of the same connector.
The relation is required in the earlier of the two normal subgroups. -/
theorem minBad_two_cyclicFactors_transfer {N M : Subgroup F}
    [N.Normal] [M.Normal] (hNM : N ≤ M)
    {c d : F} (hc : MinBad N c) (hd : MinBad M d)
    (l r p u s l' r' p' v s' : RawWord) (g : F)
    (hcword : c.toWord = l ++ r) (hcfactor : r ++ l = p ++ u ++ s)
    (hdword : d.toWord = l' ++ r') (hdfactor : r' ++ l' = p' ++ v ++ s')
    (hrel : FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹ ∈ N) :
    rawWeight u ≤ rawWeight v + 2 * weightedLength g ∧
      rawWeight v ≤ rawWeight u + 2 * weightedLength g := by
  constructor
  · exact minBad_cyclicFactor_inverse_conjugacy_weight hc l r p u s v g
      hcword hcfactor hrel
  · have he : (FreeGroup.mk u * g)⁻¹ *
        (FreeGroup.mk u * g * FreeGroup.mk v * g⁻¹) *
        ((FreeGroup.mk u * g)⁻¹)⁻¹ =
        FreeGroup.mk v * g⁻¹ * FreeGroup.mk u * (g⁻¹)⁻¹ := by group
    have hrev : FreeGroup.mk v * g⁻¹ * FreeGroup.mk u * (g⁻¹)⁻¹ ∈ M := by
      rw [← he]
      exact (inferInstance : M.Normal).conj_mem _ (hNM hrel) _
    have hwt : weightedLength g⁻¹ = weightedLength g := by
      unfold weightedLength
      rw [FreeGroup.toWord_inv, rawWeight_invRev]
    have h := minBad_cyclicFactor_inverse_conjugacy_weight hd l' r' p' v s' u
      g⁻¹ hdword hdfactor hrev
    rwa [hwt] at h

#print axioms minBad_cyclicFactor_inverse_conjugacy_weight
#print axioms minBad_two_cyclicFactors_transfer



/-! ## Literal periodic compatibility of minimal bad periods

Fine--Wilf applies to signed raw words as well as to the positive
conjugating words. This section isolates the literal compatibility
theorem; quotient equality of long sections is not literal equality.
-/

/-- A word with a period dividing its length is a literal power of
its first period block. -/
theorem rawWord_eq_pow_of_dividing_period (w : RawWord) (d k : ℕ)
    (hper : w.HasPeriod d) (hd : d ≤ w.length)
    (hlen : w.length = k*d) :
    w = rawNatPow (w.take d) k := by
  let b := w.take d
  have hb : b.length = d := by simp [b, Nat.min_eq_left hd]
  have hstep : w <+: b ++ w := hper
  have hp (n : ℕ) : w <+: rawNatPow b n ++ w := by
    induction n with
    | zero => simp [rawNatPow]
    | succ n ih =>
      have hh : rawNatPow b n ++ w <+: rawNatPow b n ++ (b ++ w) :=
        (List.prefix_append_right_inj _).mpr hstep
      simpa only [rawNatPow, List.append_assoc] using ih.trans hh
  have hlenPow (n : ℕ) : (rawNatPow b n).length = n*b.length := by
    induction n with
    | zero => simp [rawNatPow]
    | succ n ih =>
      simp only [rawNatPow, List.length_append, ih, Nat.succ_mul]
  have heq : w.length = (rawNatPow b k).length := by
    rw [hlenPow, hb]
    exact hlen
  exact ((List.isPrefix_append_of_length (le_of_eq heq)).mp (hp k)).eq_of_length heq

/-- A selected minimal bad word is nonempty and has no proper
positive period dividing its literal length. -/
theorem minBad_dividing_period {N : Subgroup F} [N.Normal] {c : F}
    (hc : MinBad N c) (d : ℕ) (hd : 0 < d)
    (hper : c.toWord.HasPeriod d) (hdvd : d ∣ c.toWord.length) :
    d = c.toWord.length := by
  have hpos : 0 < c.toWord.length := by
    by_contra! hn
    have hz : c.toWord = [] := List.length_eq_zero_iff.mp (by omega)
    have hw := weight_ge_of_bad N c hc.1
    norm_num [weightedLength, hz, rawWeight] at hw
  obtain ⟨k,hk⟩ := hdvd
  have hkpos : 0 < k := by
    by_contra! h
    have hz : k = 0 := by omega
    rw [hz, Nat.mul_zero] at hk
    omega
  by_contra hne
  have hk2 : 2 ≤ k := by
    by_contra! h
    have h1 : k = 1 := by omega
    rw [h1,Nat.mul_one] at hk
    exact hne hk.symm
  have hdle : d ≤ c.toWord.length := by
    rw [hk]
    simpa using Nat.mul_le_mul_left d (show 1 ≤ k by omega)
  have hpow := rawWord_eq_pow_of_dividing_period c.toWord d k hper hdle
    (by rw [hk, Nat.mul_comm])
  have hnonempty : c.toWord.take d ≠ [] := by
    intro h
    have he := congrArg List.length h
    simp [Nat.min_eq_left hdle] at he
    omega
  exact (minBad_not_literal_power hc (c.toWord.take d) k hnonempty hk2) hpow

/-- If two minimal bad periods begin the same sufficiently long
literal word and both lengths are periods of that word, they coincide.
The normal subgroups may be different. -/
theorem minBad_literal_period_alignment {N M : Subgroup F}
    [N.Normal] [M.Normal] {c d : F}
    (hc : MinBad N c) (hd : MinBad M d)
    (z : RawWord) (hp : c.toWord <+: z) (hq : d.toWord <+: z)
    (hperP : z.HasPeriod c.toWord.length)
    (hperQ : z.HasPeriod d.toWord.length)
    (hthreshold : c.toWord.length + d.toWord.length -
      c.toWord.length.gcd d.toWord.length ≤ z.length) :
    c = d := by
  have hpos : 0 < c.toWord.length := by
    by_contra! hn
    have hz : c.toWord = [] := List.length_eq_zero_iff.mp (by omega)
    have hw := weight_ge_of_bad N c hc.1
    norm_num [weightedLength, hz, rawWeight] at hw
  have hg := hperP.gcd hperQ hthreshold
  have hgp := hg.infix hp.isInfix
  have hgq := hg.infix hq.isInfix
  have hG := Nat.gcd_pos_of_pos_left d.toWord.length hpos
  have hP := minBad_dividing_period hc _ hG hgp (Nat.gcd_dvd_left _ _)
  have hQ := minBad_dividing_period hd _ hG hgq (Nat.gcd_dvd_right _ _)
  have hlen : c.toWord.length = d.toWord.length := hP.symm.trans hQ
  have he := (List.prefix_of_prefix_length_le hp hq (le_of_eq hlen)).eq_of_length hlen
  simpa only [FreeGroup.mk_toWord] using congrArg (FreeGroup.mk : RawWord → F) he

#print axioms rawWord_eq_pow_of_dividing_period
#print axioms minBad_dividing_period
#print axioms minBad_literal_period_alignment



/-! ## Literal cross-rank separation

Once the chosen bad word is made good by its defining relation,
it remains good in every subsequent quotient. Hence a later bad
period cannot be any cyclic rotation of it. Fine--Wilf now rules
out long literal overlaps even at different starting corners.
-/

theorem selected_period_good_next (pick : WeightedSelector)
    (X : ConjugatorChoice) (i : ℕ)
    (h : ∃ w : F, ¬ Good (weightedStages pick X i) w) :
    Good (weightedStages pick X (i+1))
      (pick (weightedStages pick X i) h).val := by
  let N := weightedStages pick X i
  let c := (pick N h).val
  refine ⟨X i N c, 1, ?_⟩
  rw [zpow_one, ← heightRelator_one (X i N c) c]
  change heightRelator (X i N c) c 1 ∈ adjoin N (weightedRelator pick X i N)
  rw [← weightedRelator_eq pick X i N h]
  exact relator_mem_adjoin _ _

/-- Goodness is invariant under cutting a literal word at a corner
and rotating the two pieces, with no reduction assumption. -/
theorem good_raw_rotation_iff (N : Subgroup F) (l r : RawWord) :
    Good N (FreeGroup.mk (r ++ l)) ↔ Good N (FreeGroup.mk (l ++ r)) := by
  have he : FreeGroup.mk l * FreeGroup.mk (r ++ l) *
      (FreeGroup.mk l)⁻¹ = FreeGroup.mk (l ++ r) := by
    simp only [← FreeGroup.mul_mk]; group
  simpa only [he] using
    (good_conjugate_iff N (FreeGroup.mk l) (FreeGroup.mk (r ++ l))).symm

/-- At two distinct active ranks, sufficiently long common literal
periodic readings cannot start with cyclic rotations of both selected
periods. This is a free-word statement; the graded quotient version
of Guba's periodic compatibility remains to be proved. -/
theorem distinct_rank_literal_period_overlap (pick : WeightedSelector)
    (X : ConjugatorChoice) (i j : ℕ) (hij : i < j)
    (hi : ∃ w : F, ¬ Good (weightedStages pick X i) w)
    (hj : ∃ w : F, ¬ Good (weightedStages pick X j) w)
    (l r p q z : RawWord)
    (hc : (pick (weightedStages pick X i) hi).val.toWord = l ++ r)
    (hd : (pick (weightedStages pick X j) hj).val.toWord = p ++ q)
    (hp : r ++ l <+: z) (hq : q ++ p <+: z)
    (hperP : z.HasPeriod (r ++ l).length)
    (hperQ : z.HasPeriod (q ++ p).length) :
    z.length < (r ++ l).length + (q ++ p).length -
      (r ++ l).length.gcd (q ++ p).length := by
  let N := weightedStages pick X i
  let M := weightedStages pick X j
  let _ : N.Normal := weightedStages_normal pick X i
  let _ : M.Normal := weightedStages_normal pick X j
  have hci : MinBad N (pick N hi).val := (pick N hi).property
  have hdj : MinBad M (pick M hj).val := (pick M hj).property
  have hcr := (minBad_rotation hci l r hc).1
  have hdr := (minBad_rotation hdj p q hd).1
  have hcw := minBad_rotation_toWord hci l r hc
  have hdw := minBad_rotation_toWord hdj p q hd
  by_contra! hlarge
  have he : FreeGroup.mk (r ++ l) = FreeGroup.mk (q ++ p) := by
    apply minBad_literal_period_alignment hcr hdr z
    · rw [hcw]; exact hp
    · rw [hdw]; exact hq
    · rw [hcw]; exact hperP
    · rw [hdw]; exact hperQ
    · rw [hcw, hdw]; exact hlarge
  have hg : Good M (pick N hi).val :=
    good_mono (weightedStages_mono pick X (Nat.succ_le_of_lt hij))
      (selected_period_good_next pick X i hi)
  have hg' : Good M (FreeGroup.mk (l ++ r)) := by
    rw [← hc, FreeGroup.mk_toWord]
    exact hg
  exact hdr.1 (he ▸ (good_raw_rotation_iff M l r).mpr hg')

#print axioms selected_period_good_next
#print axioms good_raw_rotation_iff
#print axioms distinct_rank_literal_period_overlap



/-! ## Quotient-level cross-rank obstruction

A later minimal bad period cannot be conjugate to any nonnegative
power of an earlier selected period in its preceding quotient.
The proof needs no estimate on the length of the conjugator.
It does not say that a power of the later period is bad.
-/

/-- Goodness is invariant under actual conjugacy in the quotient,
not merely conjugacy of free words. -/
theorem good_of_quotient_conj {N : Subgroup F} [N.Normal] {u v : F}
    (h : IsConj (QuotientGroup.mk' N u) (QuotientGroup.mk' N v))
    (hv : Good N v) : Good N u := by
  obtain ⟨k,hk⟩ := (good_iff_quotient N v).mp hv
  exact (good_iff_quotient N u).mpr ⟨k,h.trans hk⟩

/-- A later active period is not conjugate to any positive power
of an earlier selected period, even after imposing all relations
of ranks preceding the later period. -/
theorem distinct_rank_quotient_power_separation (pick : WeightedSelector)
    (X : ConjugatorChoice) (i j : ℕ) (hij : i < j)
    (hi : ∃ w : F, ¬ Good (weightedStages pick X i) w)
    (hj : ∃ w : F, ¬ Good (weightedStages pick X j) w)
    (m : ℕ) :
    let M := weightedStages pick X j
    letI : M.Normal := weightedStages_normal pick X j
    ¬ IsConj (QuotientGroup.mk' M (pick M hj).val)
      (QuotientGroup.mk' M ((pick (weightedStages pick X i) hi).val ^ m)) := by
  dsimp only
  let M := weightedStages pick X j
  let _ : M.Normal := weightedStages_normal pick X j
  intro h
  have hg : Good M (pick (weightedStages pick X i) hi).val :=
    good_mono (weightedStages_mono pick X (Nat.succ_le_of_lt hij))
      (selected_period_good_next pick X i hi)
  exact (pick M hj).property.1 (good_of_quotient_conj h (good_pow M hg m))

/-- A concrete lower-rank relation expressing the later selected
period as a conjugate of an earlier power is impossible. -/
theorem distinct_rank_power_relation_not_mem (pick : WeightedSelector)
    (X : ConjugatorChoice) (i j t : ℕ) (hij : i < j) (htj : t ≤ j)
    (hi : ∃ w : F, ¬ Good (weightedStages pick X i) w)
    (hj : ∃ w : F, ¬ Good (weightedStages pick X j) w)
    (m : ℕ) (g : F) :
    g * (pick (weightedStages pick X j) hj).val * g⁻¹ *
      (((pick (weightedStages pick X i) hi).val ^ m)⁻¹) ∉
        weightedStages pick X t := by
  let M := weightedStages pick X j
  let _ : M.Normal := weightedStages_normal pick X j
  let c := (pick (weightedStages pick X i) hi).val
  let d := (pick M hj).val
  let q := QuotientGroup.mk' M
  intro h
  have hm : g * d * g⁻¹ * (c ^ m)⁻¹ ∈ M :=
    weightedStages_mono pick X htj h
  have he : q (g * d * g⁻¹ * (c ^ m)⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hm
  simp only [map_mul,map_inv] at he
  have hc : IsConj (q d) (q (c ^ m)) := by
    apply isConj_iff.mpr
    refine ⟨q g,?_⟩
    calc
      _ = (q g * q d * (q g)⁻¹ * (q (c ^ m))⁻¹) * q (c ^ m) := by group
      _ = _ := by rw [he,one_mul]
  exact distinct_rank_quotient_power_separation pick X i j hij hi hj m hc

#print axioms good_of_quotient_conj
#print axioms distinct_rank_quotient_power_separation
#print axioms distinct_rank_power_relation_not_mem



/-! ## Coherent power relations in the graded quotient

A single conjugacy between nontrivial powers need not identify
the roots in an arbitrary group. Two relations with the same
conjugator and coprime exponents on the later period do suffice.
This gives an algebraic obstruction without assuming unique roots
or torsion-freeness of any stage of the presentation.
-/

/-- Good words are closed under all integer powers, including
negative powers. -/
theorem good_integer_power (N : Subgroup F) [N.Normal] {w : F}
    (hw : Good N w) (m : ℤ) : Good N (w ^ m) := by
  obtain ⟨k,hk⟩ := (good_iff_quotient N w).mp hw
  obtain ⟨g,hg⟩ := isConj_iff.mp hk
  apply (good_iff_quotient N (w ^ m)).mpr
  refine ⟨k*m, isConj_iff.mpr ⟨g,?_⟩⟩
  rw [map_zpow, zpow_mul, ← conj_zpow, hg]

/-- The common conjugator is essential. The explicit Bezout
identity avoids imposing any root-uniqueness hypothesis. -/
theorem coherent_power_conjugacy_bezout {G : Type*} [Group G]
    (c d g : G) (k l m n s t : ℤ)
    (hbez : k*s+l*t = 1)
    (h1 : g*d^k*g⁻¹ = c^m)
    (h2 : g*d^l*g⁻¹ = c^n) :
    g*d*g⁻¹ = c^(m*s+n*t) := by
  have h1' : (g*d*g⁻¹)^k = c^m := by
    rw [conj_zpow,h1]
  have h2' : (g*d*g⁻¹)^l = c^n := by
    rw [conj_zpow,h2]
  calc
    g*d*g⁻¹ = (g*d*g⁻¹)^(k*s+l*t) := by rw [hbez,zpow_one]
    _ = ((g*d*g⁻¹)^k)^s * ((g*d*g⁻¹)^l)^t := by
      simp only [zpow_add,zpow_mul]
    _ = c^(m*s+n*t) := by
      rw [h1',h2']
      simp only [zpow_add,zpow_mul]

/-- If a good period and a minimal bad period have two coherent
power relations in the quotient, their exponents on the bad side
cannot admit a Bezout identity. The input is normal-subgroup
membership of the two actual boundary products. -/
theorem minBad_coherent_power_relations_impossible
    {N : Subgroup F} [N.Normal] {c d : F}
    (hc : Good N c) (hd : MinBad N d)
    (g : F) (k l m n s t : ℤ) (hbez : k*s+l*t = 1)
    (h1 : g*d^k*g⁻¹*(c^m)⁻¹ ∈ N)
    (h2 : g*d^l*g⁻¹*(c^n)⁻¹ ∈ N) : False := by
  let q := QuotientGroup.mk' N
  have relation (p r : ℤ) (h : g*d^p*g⁻¹*(c^r)⁻¹ ∈ N) :
      q g * (q d)^p * (q g)⁻¹ = (q c)^r := by
    have he : q (g*d^p*g⁻¹*(c^r)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h
    simp only [map_mul,map_inv,map_zpow] at he
    calc
      _ = (q g * (q d)^p * (q g)⁻¹ * ((q c)^r)⁻¹) * (q c)^r := by group
      _ = _ := by rw [he,one_mul]
  have he := coherent_power_conjugacy_bezout (q c) (q d) (q g)
    k l m n s t hbez (relation k m h1) (relation l n h2)
  have hconj : IsConj (q d) (q (c^(m*s+n*t))) := by
    apply isConj_iff.mpr
    refine ⟨q g,?_⟩
    rw [map_zpow]
    exact he
  exact hd.1 (good_of_quotient_conj hconj (good_integer_power N hc _))

#print axioms good_integer_power
#print axioms coherent_power_conjugacy_bezout
#print axioms minBad_coherent_power_relations_impossible



/-! ## Rank-one smoothness: pure-a factors of a periodic section

A literal interval of at least one full period contains every letter
of that period, independently of the starting position. Since a bad
word cannot consist solely of a-letters, this yields a strict bound
on pure-a intervals in its periodic repetition. This is the literal
period-side part of the rank-one smoothness argument.
-/

/-- Every letter of an initial period occurs in any factor whose
length is at least that of the period. -/
theorem periodic_factor_contains_period_letters (c p z r : RawWord)
    (hp : c <+: p ++ z ++ r)
    (hper : (p ++ z ++ r).HasPeriod c.length)
    (hz : c.length ≤ z.length) :
    ∀ x ∈ c, x ∈ z := by
  intro x hx
  obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
  let d := c.length
  let j := p.length % d
  have hd : 0 < d := by omega
  have hj : j < d := Nat.mod_lt _ hd
  let t := if j ≤ i then i-j else d+i-j
  have ht : t < d := by
    dsimp [t]
    split <;> omega
  have hmod : (p.length+t) % d = i := by
    calc
      _ = (j+t) % d := by
        dsimp only [j]
        rw [Nat.add_mod, Nat.mod_eq_of_lt ht]
      _ = i := by
        dsimp only [t]
        split
        · rw [show j+(i-j) = i by omega, Nat.mod_eq_of_lt hi]
        · rw [show j+(d+i-j) = d+i by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt hi]
  let w := p ++ z ++ r
  have hidx : p.length+t < w.length := by
    dsimp [w]
    simp only [List.length_append]
    omega
  have hpre : w[i]? = some x := by
    have h := (List.prefix_iff_getElem?.mp hp) i hi
    rw [hix] at h
    exact h
  have he := hper.getElem?_mod d (p.length+t) w hidx
  rw [hmod,hpre] at he
  have hzt : t < z.length := lt_of_lt_of_le ht hz
  have hread : w[p.length+t]? = z[t]? := by
    dsimp only [w]
    rw [List.append_assoc]
    rw [List.getElem?_append_right (by omega : p.length ≤ p.length+t)]
    rw [show p.length+t-p.length = t by omega]
    exact List.getElem?_append_left hzt
  exact List.mem_of_getElem? (hread.symm.trans he.symm)

/-- Unlike a small-weight bound, this recognizes arbitrarily long
words consisting only of signed a-letters. -/
theorem pure_a_word_eval (w : RawWord) (hw : ∀ x ∈ w, x.1 = 0) :
    ∃ n : ℤ, FreeGroup.mk w = a^n := by
  induction w with
  | nil => exact ⟨0, by rw [zpow_zero, FreeGroup.one_eq_mk]⟩
  | cons x xs ih =>
    have hx := hw x (List.mem_cons_self)
    obtain ⟨n,hn⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    rcases x with ⟨i,s⟩
    change i = 0 at hx
    subst i
    have hmul : FreeGroup.mk ((0,s)::xs) =
        FreeGroup.mk [(0,s)] * FreeGroup.mk xs := by
      exact (FreeGroup.mul_mk (L₁ := [(0,s)]) (L₂ := xs)).symm
    cases s with
    | false =>
      refine ⟨-1+n,?_⟩
      rw [hmul,FreeGroup.mk_eq_inv_of,hn,zpow_add]
      simp [a]
    | true =>
      refine ⟨1+n,?_⟩
      rw [hmul,FreeGroup.mk_eq_of,hn,zpow_add]
      simp [a]

theorem pure_a_word_weight (w : RawWord) (hw : ∀ x ∈ w, x.1 = 0) :
    rawWeight w = w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    have hx := hw x List.mem_cons_self
    have hxs := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    change letterWeight x + rawWeight xs = xs.length+1
    rw [hxs]
    simp [letterWeight,hx,Nat.add_comm]

/-- The pure-a interval of a bad periodic word is shorter in Guba's
weighted metric than the original period. No restriction on the
number of repetitions or on the position of the interval is needed. -/
theorem bad_period_pure_a_factor_bound {N : Subgroup F} {c : F}
    (hc : ¬ Good N c) (p z r : RawWord)
    (hp : c.toWord <+: p ++ z ++ r)
    (hper : (p ++ z ++ r).HasPeriod c.toWord.length)
    (ha : ∀ x ∈ z, x.1 = 0) :
    rawWeight z < weightedLength c := by
  have hlen : z.length < c.toWord.length := by
    by_contra! h
    have hall := periodic_factor_contains_period_letters c.toWord p z r hp hper h
    obtain ⟨n,hn⟩ := pure_a_word_eval c.toWord (fun x hx => ha x (hall x hx))
    rw [FreeGroup.mk_toWord] at hn
    exact hc (hn.symm ▸ good_a_zpow N n)
  rw [pure_a_word_weight z ha]
  exact hlen.trans_le (length_le_rawWeight c.toWord)

#print axioms periodic_factor_contains_period_letters
#print axioms pure_a_word_eval
#print axioms pure_a_word_weight
#print axioms bad_period_pure_a_factor_bound



/-! ## Rank-one smoothness: special positive conjugators

Cube-freeness bounds zero runs in a prefix by two letters. Joining
copies can at most double this bound; the bbb separators prevent
any further increase when the long blocks are concatenated.
-/

theorem guba_prefix_zero_factor_bound (m : ℕ) (z : List (Fin 2))
    (hz : z <:+: gubaEvenPrefix m) (ha : ∀ x ∈ z, x = 0) :
    z.length ≤ 2 := by
  obtain ⟨p,r,he⟩ := hz
  have hper : z.HasPeriod 1 := by
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    have hi' : i < z.length := by omega
    have hi'' : i+1 < z.length := by omega
    rw [getElem?_pos z i hi', getElem?_pos z (i+1) hi'']
    have h1 : z[i] = 0 := ha _ (List.mem_of_getElem (l := z) (i := i) rfl)
    have h2 : z[i+1] = 0 := ha _ (List.mem_of_getElem (l := z) (i := i+1) rfl)
    rw [h1,h2]
  have h := thueFactor_period_bound (prefixEnd (2*m+1)+1) 1 p z r
    he.symm (by omega) hper
  omega

theorem zero_prefix_repeat_bound (q : List (Fin 2)) (n : ℕ)
    (hb : (1 : Fin 2) ∈ q)
    (hbound : ∀ z : List (Fin 2), z <:+: q → (∀ x ∈ z, x = 0) → z.length ≤ 2)
    (z : List (Fin 2)) (hz : z <+: (List.replicate n q).flatten)
    (ha : ∀ x ∈ z, x = 0) :
    z.length ≤ 2 := by
  cases n with
  | zero =>
    have he : z = [] := List.prefix_nil.mp (by simpa using hz)
    simp [he]
  | succ n =>
    rw [List.replicate_succ,List.flatten_cons] at hz
    rcases List.prefix_or_prefix_of_prefix hz (List.prefix_append q _) with h | h
    · exact hbound z h.isInfix ha
    · exact False.elim (by
        have he := ha 1 (h.mem hb)
        exact (by decide : (1 : Fin 2) ≠ 0) he)

theorem zero_factor_repeat_bound (q : List (Fin 2)) (n : ℕ)
    (hb : (1 : Fin 2) ∈ q)
    (hbound : ∀ z : List (Fin 2), z <:+: q → (∀ x ∈ z, x = 0) → z.length ≤ 2)
    (z : List (Fin 2)) (hz : z <:+: (List.replicate n q).flatten)
    (ha : ∀ x ∈ z, x = 0) :
    z.length ≤ 4 := by
  induction n generalizing z with
  | zero =>
    have he : z.length ≤ ([] : List (Fin 2)).length :=
      hz.sublist.length_le
    simpa using (le_trans he (by decide : ([] : List (Fin 2)).length ≤ 4))
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons] at hz
    rcases List.infix_append_iff.mp hz with h | h | ⟨u,v,rfl,hu,hv⟩
    · exact (hbound z h ha).trans (by omega)
    · exact ih z h ha
    · have h1 := hbound u hu.isInfix (fun x hx => ha x (List.mem_append_left _ hx))
      have h2 := zero_prefix_repeat_bound q n hb hbound v hv
        (fun x hx => ha x (List.mem_append_right _ hx))
      rw [List.length_append]
      omega

theorem zero_factor_longBlock_bound (q : List (Fin 2)) (n : ℕ)
    (hb : (1 : Fin 2) ∈ q)
    (hbound : ∀ z : List (Fin 2), z <:+: q → (∀ x ∈ z, x = 0) → z.length ≤ 2)
    (z : List (Fin 2)) (hz : z <:+: longBlock q n)
    (ha : ∀ x ∈ z, x = 0) :
    z.length ≤ 4 := by
  have empty (u : List (Fin 2)) (hu : u <:+: List.replicate 3 (1 : Fin 2))
      (hau : ∀ x ∈ u, x = 0) : u = [] := by
    cases u with
    | nil => rfl
    | cons x xs =>
      have hmem := hu.sublist.subset (List.mem_cons_self : x ∈ x::xs)
      have hx : x = 1 := List.eq_of_mem_replicate hmem
      have h0 := hau x List.mem_cons_self
      exact False.elim ((by decide : (1 : Fin 2) ≠ 0) (hx.symm.trans h0))
  unfold longBlock at hz
  rcases List.infix_append_iff.mp hz with h | h | ⟨u,v,rfl,hu,hv⟩
  · rw [empty z h ha]
    decide
  · exact zero_factor_repeat_bound q (n+1) hb hbound z h ha
  · have he := empty u hu.isInfix (fun x hx => ha x (List.mem_append_left _ hx))
    subst u
    exact zero_factor_repeat_bound q (n+1) hb hbound v hv.isInfix (by simpa using ha)

theorem zero_prefix_longBlock_empty (q : List (Fin 2)) (n : ℕ)
    (z : List (Fin 2)) (hz : z <+: longBlock q n)
    (ha : ∀ x ∈ z, x = 0) : z = [] := by
  have h1 : [(1 : Fin 2)] <+: longBlock q n := by
    unfold longBlock
    simp [List.replicate_succ]
  rcases List.prefix_or_prefix_of_prefix hz h1 with h | h
  · have hlen := h.length_le
    cases z with
    | nil => rfl
    | cons x xs =>
      have hx : x = 1 := by
        simpa using (List.cons_prefix_cons.mp h).1
      have h0 := ha x List.mem_cons_self
      exact False.elim ((by decide : (1 : Fin 2) ≠ 0) (hx.symm.trans h0))
  · exact False.elim ((by decide : (1 : Fin 2) ≠ 0) (ha 1 (h.mem (by simp))))

/-- All zero runs in the actual long conjugator have length at most
four, regardless of the number of blocks. -/
theorem guba_longRaw_zero_factor_bound (m n : ℕ)
    (z : List (Fin 2)) (hz : z <:+: longRaw (gubaEvenPrefix m) n)
    (ha : ∀ x ∈ z, x = 0) : z.length ≤ 4 := by
  let q := gubaEvenPrefix m
  have hb : (1 : Fin 2) ∈ q := by
    exact List.mem_of_getElem (gubaPrefix_second (2*m+1))
  have hbound := guba_prefix_zero_factor_bound m
  induction n generalizing z with
  | zero =>
    have he : z.length ≤ ([] : List (Fin 2)).length :=
      hz.sublist.length_le
    simpa using (le_trans he (by decide : ([] : List (Fin 2)).length ≤ 4))
  | succ n ih =>
    rw [longRaw] at hz
    rcases List.infix_append_iff.mp hz with h | h | ⟨u,v,rfl,hu,hv⟩
    · exact ih z h ha
    · exact zero_factor_longBlock_bound q n hb hbound z h ha
    · have he := zero_prefix_longBlock_empty q n v hv
        (fun x hx => ha x (List.mem_append_right _ hx))
      subst v
      simp only [List.append_nil] at ha ⊢
      exact ih u hu.isInfix ha

#print axioms guba_prefix_zero_factor_bound
#print axioms zero_prefix_repeat_bound
#print axioms zero_factor_repeat_bound
#print axioms zero_factor_longBlock_bound
#print axioms zero_prefix_longBlock_empty
#print axioms guba_longRaw_zero_factor_bound



/-- The bound of four applies to the actual rank-dependent choice
of the positive conjugating word, with signed-letter weights. -/
theorem activeLongWord_pure_a_weight_bound (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (z : List (Fin 2)) (hz : z <:+: activeLongWord pick i h)
    (ha : ∀ x ∈ z, x = 0) : positiveWeight z ≤ 4 := by
  have hlen : z.length ≤ 4 := by
    exact guba_longRaw_zero_factor_bound
      (chooseEvenPrefixIndex (pick (gubaState pick i).1 h).val (gubaState pick i).2)
      (10^20) z hz ha
  have hmap : ∀ x ∈ z.map (fun x => (x,true)), x.1 = 0 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact ha y hy
  rw [positiveWeight_eq_rawWeight_map, pure_a_word_weight _ hmap, List.length_map]
  exact hlen

/-- A uniform relative bound using only the actual chosen prefix
weight. The large margin is useful when later dividing a long
side into sections. No geometric smoothness condition is asserted. -/
theorem activeLongWord_pure_a_relative_bound (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (z : List (Fin 2)) (hz : z <:+: activeLongWord pick i h)
    (ha : ∀ x ∈ z, x = 0) :
    10^37 * positiveWeight z < positiveWeight (activePrefix pick i h) := by
  calc
    _ ≤ 10^37 * 4 := Nat.mul_le_mul_left _ (activeLongWord_pure_a_weight_bound pick i h z hz ha)
    _ < 6*10^80 := by norm_num
    _ ≤ _ := activePrefix_weight_ge pick i h

#print axioms activeLongWord_pure_a_weight_bound
#print axioms activeLongWord_pure_a_relative_bound



/-! ## Signed section readings of the actual rank rows

Transfer the pure-a bounds to the signed alphabet used by the
ribbon, including the reverse orientation. This avoids treating
an inverse side as a new independent positive word.
-/

theorem invRev_infix_of_infix {u v : RawWord} (h : u <:+: v) :
    FreeGroup.invRev u <:+: FreeGroup.invRev v := by
  obtain ⟨p,r,he⟩ := h
  refine ⟨FreeGroup.invRev r, FreeGroup.invRev p, ?_⟩
  rw [← he, FreeGroup.invRev_append, FreeGroup.invRev_append, List.append_assoc]

theorem invRev_pure_a {v : RawWord} (ha : ∀ x ∈ v, x.1 = 0) :
    ∀ x ∈ FreeGroup.invRev v, x.1 = 0 := by
  intro x hx
  rw [FreeGroup.invRev, List.mem_reverse] at hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact ha y hy

/-- The actual signed positive side inherits the bound without
assuming a positive factor decomposition as extra input. -/
theorem activeLongWord_signed_pure_a_bound (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (v : RawWord)
    (hv : v <:+: (activeLongWord pick i h).map (fun x => (x,true)))
    (ha : ∀ x ∈ v, x.1 = 0) :
    rawWeight v ≤ 4 := by
  obtain ⟨p,r,he⟩ := hv
  obtain ⟨dp,dz,dr,hds,hp,hz,hr⟩ :=
    read_factor_lift (fun x : Fin 2 => (x,true)) (activeLongWord pick i h)
      p v r he.symm
  have hf : dz <:+: activeLongWord pick i h := ⟨dp,dr,hds.symm⟩
  have hz0 : ∀ x ∈ dz, x = 0 := by
    intro x hx
    have hm : (x,true) ∈ v := by
      rw [← hz]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩
    exact ha (x,true) hm
  rw [← hz, ← positiveWeight_eq_rawWeight_map]
  exact activeLongWord_pure_a_weight_bound pick i h dz hf hz0

/-- In either orientation of the actual special side, a pure-a
interval has weight at most four. The factor is a signed reading
of the literal side, not a representative chosen in the quotient. -/
theorem activeLongWord_either_side_pure_a_bound (pick : WeightedSelector) (i : ℕ)
    (h : ∃ w : F, ¬ Good (gubaState pick i).1 w)
    (v : RawWord)
    (hv : v <:+: (activeLongWord pick i h).map (fun x => (x,true)) ∨
      v <:+: FreeGroup.invRev ((activeLongWord pick i h).map (fun x => (x,true))))
    (ha : ∀ x ∈ v, x.1 = 0) :
    rawWeight v ≤ 4 := by
  rcases hv with hp | hn
  · exact activeLongWord_signed_pure_a_bound pick i h v hp ha
  · have hf := invRev_infix_of_infix hn
    rw [FreeGroup.invRev_invRev] at hf
    have hw := activeLongWord_signed_pure_a_bound pick i h (FreeGroup.invRev v)
      hf (invRev_pure_a ha)
    rwa [rawWeight_invRev] at hw

#print axioms invRev_infix_of_infix
#print axioms invRev_pure_a
#print axioms activeLongWord_signed_pure_a_bound
#print axioms activeLongWord_either_side_pure_a_bound



/-! ## Lemma 23: removing the designated cell (algebraic part)

Guba, pp. 258--259, removes a cell and invokes induction on a
strictly smaller type. The Peiffer expression of the remaining
filling is minimal for its based boundary product. Prove that
fact together with strict type descent and the exact boundary
equation. A regular annular geometric realization, with the
designated two boundary cycles, is a separate obligation.
-/

theorem guba23_delete_cell_minimal_type
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ [x] ++ r)) :
    let rel := rankHeightRel pick X n
    let y := shiftOccurrence (Peiffer.evaluation rel p) x
    let v := Peiffer.evaluation rel (p ++ r)
    Peiffer.term rel y * v = w ∧
      RankMinimalExpression pick X n v (p ++ r) ∧
      descendingCountLT n rankCount (p ++ r) (p ++ [x] ++ r) := by
  dsimp only
  let rel := rankHeightRel pick X n
  let y := shiftOccurrence (Peiffer.evaluation rel p) x
  have hterm : Peiffer.evaluation rel [y] = Peiffer.term rel y := by
    simp [Peiffer.evaluation]
  have he : Peiffer.evaluation rel (p ++ [x] ++ r) =
      Peiffer.evaluation rel ([y] ++ (p ++ r)) := by
    rw [peiffer_evaluation_append, peiffer_move_occurrence rel p x]
    simp only [peiffer_evaluation_append, y]
    group
  have hc (j : ℕ) : rankCount ([y] ++ (p ++ r)) j =
      rankCount (p ++ [x] ++ r) j := by
    simp only [rankCount_append,rankCount_singleton,y,shiftOccurrence]
    omega
  have hmin : RankMinimalExpression pick X n w ([y] ++ (p ++ r)) := by
    refine ⟨he.symm.trans hs.1,?_⟩
    intro t ht j hj habove
    rw [hc j]
    exact hs.2 t ht j hj (fun k hjk hkn => (hc k).symm.trans (habove k hjk hkn))
  refine ⟨?_,⟨rfl,?_⟩,?_⟩
  · have h := hmin.1
    change Peiffer.evaluation rel ([y] ++ (p ++ r)) = w at h
    rw [peiffer_evaluation_append,hterm] at h
    exact h
  · intro t ht j hj habove
    have ht' : Peiffer.evaluation rel ([y] ++ t) = w := by
      rw [peiffer_evaluation_append, ht]
      have hh := hmin.1
      simpa only [peiffer_evaluation_append] using hh
    have hcounts : ∀ k, j < k → k < n →
        rankCount ([y] ++ (p ++ r)) k = rankCount ([y] ++ t) k := by
      intro k hjk hkn
      exact (rankCount_append [y] (p ++ r) k).trans
        ((congrArg (fun z : ℕ => rankCount [y] k + z) (habove k hjk hkn)).trans
          (rankCount_append [y] t k).symm)
    have hle := hmin.2 ([y] ++ t) ht' j hj hcounts
    rw [rankCount_append [y] (p ++ r) j, rankCount_append [y] t j] at hle
    exact Nat.le_of_add_le_add_left hle
  · exact rank_type_lt_of_omitted_occurrence p r x (p ++ r) (List.Sublist.refl _)

#print axioms guba23_delete_cell_minimal_type



/-- After a cell is designated as the inner boundary, a competing
filling may change its connecting path. Minimality of the original
disc still forbids a smaller graded type of the remaining cells:
reinsert the designated cell with its new base and compare discs.

This is the algebraic annular minimality statement. It does not
assert regularity or that every geometric annular filling admits
the required based Peiffer expression with its exact cell counts. -/
theorem guba23_delete_cell_variable_base_minimal
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ [x] ++ r))
    (g : F) (t : Peiffer.Sequence F (RankHeight n))
    (ht : Peiffer.evaluation (rankHeightRel pick X n)
      ([shiftOccurrence g x] ++ t) = w) :
    ¬ descendingCountLT n rankCount t (p ++ r) := by
  rintro ⟨j,hj,hstrict,habove⟩
  have hcounts : ∀ k, j < k → k < n →
      rankCount (p ++ [x] ++ r) k =
        rankCount ([shiftOccurrence g x] ++ t) k := by
    intro k hjk hkn
    have hk := habove k hjk hkn
    simp only [rankCount_append,rankCount_singleton,shiftOccurrence] at hk ⊢
    omega
  have hle := hs.2 ([shiftOccurrence g x] ++ t) ht j hj hcounts
  simp only [rankCount_append,rankCount_singleton,shiftOccurrence] at hle hstrict
  omega

#print axioms guba23_delete_cell_variable_base_minimal



/-! ### Faithful cell indexing for the deletion step

A rank-minimal expression contains no trivial row. Consequently the
outer boundary (when nontrivial) and every interior occurrence have
a genuine zero corner in the existing ribbon; no zero-length row
is silently dropped when counting types.
-/

theorem rankMinimal_no_trivial_occurrence
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ [x] ++ r)) :
    Peiffer.term (rankHeightRel pick X n) x ≠ 1 := by
  intro he
  have hb : Peiffer.evaluation (rankHeightRel pick X n) [x] =
      Peiffer.evaluation (rankHeightRel pick X n) [] := by
    simpa [Peiffer.evaluation] using he
  apply rankMinimal_block_no_reduction pick X n w p [x] r [] hs hb
    x.1.2.1.val x.1.2.1.isLt
  · intro k hk _
    rw [rankCount_singleton]
    simp [rankCount,ne_of_lt hk]
  · rw [rankCount_singleton]
    simp [rankCount]

theorem rankMinimal_designated_row_nonempty
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ [x] ++ r)) :
    rankHeightRows pick X n x.1.2 ≠ [] := by
  intro hnil
  have hrel : rankHeightRel pick X n x.1.2 = 1 := by
    rw [← rankHeightRows_eval pick X n x.1.2, hnil, ← FreeGroup.one_eq_mk]
  apply rankMinimal_no_trivial_occurrence pick X n w p r x hs
  rcases x with ⟨⟨u,i⟩,b⟩
  cases b <;> simp [Peiffer.term] at hrel ⊢ <;> simp [hrel]

#print axioms rankMinimal_no_trivial_occurrence
#print axioms rankMinimal_designated_row_nonempty



/-- The designated occurrence determines a genuine second boundary
cycle in the existing spherical ribbon, with its exact signed word.
The occurrence index, rather than the row label, distinguishes it
from every other copy of the same relator. Marking it does not alter
the permutations. Connectedness of the two marked vertices and the
regularity conditions of Guba's annulus still need to be proved. -/
theorem guba23_designated_boundary_cycle
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w (p ++ [x] ++ r))
    (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) (p ++ [x] ++ r) = w) :
    let s := p ++ [x] ++ r
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∃ d : DiscDarts (markedRows rows w) (boundaryIdentity s),
      (discOccurrence (markedRows rows w) (boundaryIdentity s) d).val = p.length+1 ∧
      ¬ P.rotation.SameCycle z d ∧
      (P.vertexBoundary d).map read = orientedWord (rows x.1.2) x.2 ∧
      (∀ e, P.rotation.SameCycle d e ↔
        (discOccurrence (markedRows rows w) (boundaryIdentity s) e).val = p.length+1) := by
  classical
  intro s rows P z read
  let j : Fin (boundaryIdentity s).length := ⟨p.length+1,by
    simp [s,boundaryIdentity]⟩
  have hx : s[p.length]? = some x := by
    dsimp only [s]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hj : (boundaryIdentity s)[j] = markOccurrence x := by
    have hopt : (boundaryIdentity s)[p.length+1]? = some (markOccurrence x) := by
      change (s.map markOccurrence)[p.length]? = _
      rw [List.getElem?_map,hx]
      rfl
    obtain ⟨hj',hh⟩ := List.getElem?_eq_some_iff.mp hopt
    exact hh
  have hp : 0 < (orientedWord
      (markedRows rows w (boundaryIdentity s)[j].1.2)
      (boundaryIdentity s)[j].2).length := by
    rw [hj, orientedWord_length]
    change 0 < (rows x.1.2).length
    exact List.length_pos_iff.mpr (rankMinimal_designated_row_nonempty pick X n w p r x hm)
  let d := discAt (markedRows rows w) (boundaryIdentity s) j ⟨0,hp⟩
  have hd : discOccurrence (markedRows rows w) (boundaryIdentity s) d = j :=
    discOccurrence_at _ _ _ _
  refine ⟨d,congrArg Fin.val hd,?_,?_,?_⟩
  · intro h
    have he := (boundaryDart_sameVertex_iff rows w s hs hw d).mp h
    rw [hd] at he
    have hval := congrArg Fin.val he
    change p.length+1 = 0 at hval
    omega
  · have hi : (boundaryIdentity s)[j].1.2 = some x.1.2 := by
      rw [hj]
      rfl
    have hread := boundaryRibbon_interior_read rows w s hs j x.1.2 hi hp
    change (P.vertexBoundary d).map read = _ at hread
    rw [hj] at hread
    exact hread
  · intro e
    change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle d e ↔ _
    rw [disc_sameCycle_iff,hd]
    constructor
    · intro h
      exact congrArg Fin.val h.symm
    · intro h
      exact Fin.ext h.symm

#print axioms guba23_designated_boundary_cycle



/-! ### Exact vertex factorization under a spanning-tree splice

For connectedness of a rank-minimal ribbon we need more than
normal-closure membership of a component's boundary. We need a
Peiffer expression that uses the retained vertices with their
original multiplicity. Expand one splice into precisely its two
original vertex products; unchanged vertices introduce no factor.
-/


theorem guba23_splice_expand_vertex_product {D K : Type}
    [Fintype D] [Group K] (P : RibbonMap D) (v : D → K)
    (c d : D) (hn : ¬ P.rotation.SameCycle c (P.edge c))
    (hd : (P.edgeSplice c).rotation.SameCycle (P.rotation c) d)
    (g : K) :
    ∃ u t : K, g * cycleProduct (P.edgeSplice c).rotation v d * g⁻¹ =
      (u * cycleProduct P.rotation v c * u⁻¹) *
      (t * cycleProduct P.rotation v (P.edge c) * t⁻¹) := by
  have hnc : ¬ P.rotation.SameCycle (P.rotation c) (P.edge c) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  obtain ⟨k,hk⟩ := guba22_cycleProduct_conjugator
    (P.edgeSplice c).rotation v (P.rotation c) d hd
  have hc : P.rotation.SameCycle c (P.rotation c) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  obtain ⟨j,hj⟩ := guba22_cycleProduct_conjugator P.rotation v c (P.rotation c) hc
  have hmerge : cycleProduct (P.edgeSplice c).rotation v (P.rotation c) =
      cycleProduct P.rotation v (P.rotation c) *
        cycleProduct P.rotation v (P.edge c) :=
    cycleProduct_cutAt_merge P.rotation v (P.rotation c) (P.edge c) hnc
  refine ⟨g*k*j,g*k,?_⟩
  rw [hk,hmerge,hj]
  group

/-- A vertex outside the merged cycle retains its original based
product. This is the other case in the multiplicity-preserving
expansion, with no extra occurrences. -/
theorem guba23_splice_keep_vertex_product {D K : Type}
    [Fintype D] [Group K] (P : RibbonMap D) (v : D → K)
    (c d : D) (hn : ¬ P.rotation.SameCycle c (P.edge c))
    (hd : ¬ (P.edgeSplice c).rotation.SameCycle (P.rotation c) d) :
    cycleProduct (P.edgeSplice c).rotation v d = cycleProduct P.rotation v d := by
  have hnc : ¬ P.rotation.SameCycle (P.rotation c) (P.edge c) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  have ha : ¬ P.rotation.SameCycle d (P.rotation c) := by
    intro h
    exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h.symm)
  have hb : ¬ P.rotation.SameCycle d (P.edge c) := by
    intro h
    have hh : (P.edgeSplice c).rotation.SameCycle (P.rotation c) (P.edge c) :=
      cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc
    exact hd (hh.trans (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h.symm))
  exact cycleProduct_cutAt_unchanged P.rotation v _ _ _ ha hb

#print axioms guba23_splice_expand_vertex_product
#print axioms guba23_splice_keep_vertex_product



/-- The spherical boundary identity with exact cell multiplicity.
Each non-root vertex occurs once, represented by a dart and a
conjugating element. Induction merges the root with one adjacent
vertex and expands that merge on return. This supplies the
multiplicity information missing from normal-closure membership. -/
theorem guba23_component_exact_vertex_product {D K : Type}
    [Fintype D] [Group K] (P : RibbonMap D) (v : D → K)
    (he : ∀ d, v (P.edge d) = (v d)⁻¹)
    (hc : P.Connected) (hE : P.EulerEquality) (a : D) :
    ∃ l : List (K × D),
      (∀ z ∈ l, ¬ P.rotation.SameCycle a z.2) ∧
      l.Pairwise (fun x y => ¬ P.rotation.SameCycle x.2 y.2) ∧
      (∀ d, ¬ P.rotation.SameCycle a d →
        ∃ z ∈ l, P.rotation.SameCycle z.2 d) ∧
      cycleProduct P.rotation v a *
        (l.map (fun z => z.1 * cycleProduct P.rotation v z.2 * z.1⁻¹)).prod = 1 := by
  classical
  by_cases hroot : ∀ d, P.rotation.SameCycle a d
  · refine ⟨[],by simp,.nil,?_,?_⟩
    · intro d hd
      exact (hd (hroot d)).elim
    · simp only [List.map_nil,List.prod_nil,mul_one]
      apply RibbonMap.boundary_product_one D P v he hc hE
      intro d hd
      exact (hd (hroot d)).elim
  · push Not at hroot
    obtain ⟨b,hb⟩ := hroot
    obtain ⟨c,hac,hce⟩ := guba22_exists_leaving_edge P hc a b hb
    have hn : ¬ P.rotation.SameCycle c (P.edge c) :=
      fun h => hce (hac.trans h)
    let S := P.edgeSplice c
    let e := P.edge c
    let f := P.rotation c
    have hnc : ¬ P.rotation.SameCycle f e := by
      simpa only [f,e,Equiv.Perm.sameCycle_apply_left] using hn
    have haf : P.rotation.SameCycle a f :=
      hac.trans (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    have hfe : S.rotation.SameCycle f e :=
      cutAt_sameCycle_of_not_sameCycle P.rotation _ _ hnc
    obtain ⟨k,hk⟩ := guba22_cycleProduct_conjugator P.rotation v a f haf
    have hm : cycleProduct S.rotation v f =
        (k * cycleProduct P.rotation v a * k⁻¹) * cycleProduct P.rotation v e := by
      rw [show cycleProduct S.rotation v f =
        cycleProduct P.rotation v f * cycleProduct P.rotation v e from
          cycleProduct_cutAt_merge P.rotation v f e hnc, hk]
    obtain ⟨l,hl,hsep,hcov,hprod⟩ := guba23_component_exact_vertex_product S v
      (fun d => he d) (guba22_edgeSplice_connected P hc c hn)
      ((P.edgeSplice_euler_iff c hn).mpr hE) f
    have outside (d : D) (hd : ¬ S.rotation.SameCycle f d) :
        ¬ P.rotation.SameCycle a d ∧ ¬ P.rotation.SameCycle e d := by
      constructor
      · intro h
        exact hd (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc (haf.symm.trans h))
      · intro h
        exact hd (hfe.trans (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc h))
    let shift : K × D → K × D := fun z => (k⁻¹ * z.1,z.2)
    refine ⟨(k⁻¹,e) :: l.map shift,?_,?_,?_,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact hce
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
        exact (outside y.2 (hl y hy)).1
    · apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
        exact (outside y.2 (hl y hy)).2
      · apply hsep.map
        intro x y hxy hP
        exact hxy (sameCycle_cutAt_of_sameCycle P.rotation _ _ hnc hP)
    · intro d hd
      by_cases h : P.rotation.SameCycle e d
      · exact ⟨(k⁻¹,e),List.mem_cons_self,h⟩
      · have hnS : ¬ S.rotation.SameCycle f d := by
          intro hh
          rcases (P.edgeSplice_sameVertex_iff c hn _ _).mp hh with h' | h'
          · exact hd (haf.trans h')
          · rcases h'.2 with h' | h'
            · exact hd (hac.trans h'.symm)
            · exact h h'.symm
        obtain ⟨y,hy,hyS⟩ := hcov d hnS
        refine ⟨shift y,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨y,hy,rfl⟩),?_⟩
        rcases (P.edgeSplice_sameVertex_iff c hn _ _).mp hyS with hh | hh
        · exact hh
        · rcases hh.1 with hh' | hh'
          · exact ((outside y.2 (hl y hy)).1 (hac.trans hh'.symm)).elim
          · exact ((outside y.2 (hl y hy)).2 hh'.symm).elim
    · have hp (t : List (K × D)) (ht : ∀ z ∈ t, ¬ S.rotation.SameCycle f z.2) :
          ((t.map shift).map (fun z => z.1 * cycleProduct P.rotation v z.2 * z.1⁻¹)).prod =
            k⁻¹ * (t.map (fun z => z.1 * cycleProduct S.rotation v z.2 * z.1⁻¹)).prod * k := by
        induction t with
        | nil => simp
        | cons z zs ih =>
          have hz := ht z List.mem_cons_self
          have hz' := guba23_splice_keep_vertex_product P v c z.2 hn hz
          simp only [List.map_cons,List.prod_cons,shift]
          rw [ih (fun y hy => ht y (List.mem_cons_of_mem _ hy)),hz']
          group
      simp only [List.map_cons,List.prod_cons]
      rw [hp l hl]
      have hfinal := congrArg (fun x : K => k⁻¹ * x * k) hprod
      rw [hm] at hfinal
      simp only [mul_one,inv_mul_cancel] at hfinal
      convert hfinal using 1; group
termination_by Fintype.card P.Vertex
decreasing_by
  have hcount := (P.edgeSplice_counts c hn).1
  change Fintype.card (P.edgeSplice c).Vertex < Fintype.card P.Vertex
  omega

#print axioms guba23_component_exact_vertex_product



/-- Apply exact spherical factorization to the *existing* component
of the marked boundary. Every representative carries its original
occurrence index; no two retained factors can use the same index.
The product is the original boundary element, not just an element
of a normal closure. -/
theorem guba23_boundary_component_exact_factors (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let _C := P.componentRibbon z
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
    ∃ l : List (F × {d // P.SameComponent z d}),
      (∀ t ∈ l, idx t.2.val ≠ boundaryOccurrence s) ∧
      l.Pairwise (fun t u => idx t.2.val ≠ idx u.2.val) ∧
      (∀ d : {d // P.SameComponent z d}, idx d.val ≠ boundaryOccurrence s →
        ∃ t ∈ l, idx t.2.val = idx d.val) ∧
      (l.map (fun t => t.1 * FreeGroup.mk ((P.vertexBoundary t.2.val).map read) *
        t.1⁻¹)).prod = w := by
  classical
  intro P z C read idx
  let a : {d // P.SameComponent z d} := ⟨z,Relation.EqvGen.refl z⟩
  let v : {d // P.SameComponent z d} → F := fun d => FreeGroup.mk [read d.val]
  have he : ∀ d, v (C.edge d) = (v d)⁻¹ := by
    intro d
    change FreeGroup.mk [read (P.edge d.val)] = (FreeGroup.mk [read d.val])⁻¹
    have hread : read (P.edge d.val) = reverseLetter (read d.val) :=
      relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
        (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs) d.val
    rw [hread]
    exact signedLetterValue_reverse _
  have hEC : C.EulerEquality := by
    change Fintype.card C.Vertex + Fintype.card C.Face =
      Fintype.card C.Edge + 2 * Fintype.card C.Component
    rw [P.componentRibbon_card_components, mul_one]
    exact P.componentRibbon_sphere (boundaryRibbon_euler rows w s hs) z
  have same (d e : {d // P.SameComponent z d}) :
      C.rotation.SameCycle d e ↔ idx d.val = idx e.val := by
    have h := P.restrict_sameVertex_iff (P.SameComponent z)
      (P.component_membership_edge z) (P.component_membership_rotation z) d e
    exact h.trans (disc_sameCycle_iff _ _ _ _)
  have hidx : idx a.val = boundaryOccurrence s := boundaryDart_occurrence rows w s hw
  have hv (d : {d // P.SameComponent z d}) :
      cycleProduct C.rotation v d =
        FreeGroup.mk ((P.vertexBoundary d.val).map read) := by
    change ((C.vertexBoundary d).map v).prod = _
    rw [← component_vertex_read P read z d, rawWord_eval_prod, List.map_map]
    rfl
  obtain ⟨l,hl,hsep,hcov,hprod⟩ := guba23_component_exact_vertex_product C v he
    (P.componentRibbon_connected z) hEC a
  refine ⟨l,?_,?_,?_,?_⟩
  · intro t ht h
    exact hl t ht ((same a t.2).mpr (hidx.trans h.symm))
  · apply hsep.imp
    intro t u htu h
    exact htu ((same t.2 u.2).mpr h)
  · intro d hd
    obtain ⟨t,ht,h⟩ := hcov d (fun h => hd (((same a d).mp h).symm.trans hidx))
    exact ⟨t,ht,(same t.2 d).mp h⟩
  · have hroot : cycleProduct C.rotation v a = w⁻¹ := by
      rw [hv, boundaryRibbon_read rows w s hs hw, ← FreeGroup.inv_mk,FreeGroup.mk_toWord]
    simp only [hv] at hprod
    have hroot' : FreeGroup.mk ((P.vertexBoundary a.val).map read) = w⁻¹ :=
      (hv a).symm.trans hroot
    rw [hroot'] at hprod
    calc
      _ = w * (w⁻¹ * (l.map (fun t => t.1 *
        FreeGroup.mk ((P.vertexBoundary t.2.val).map read) * t.1⁻¹)).prod) := by group
      _ = w := by rw [hprod,mul_one]

#print axioms guba23_boundary_component_exact_factors



/-- Rank-minimality forbids a replacement using a proper subset of
the original occurrence indices, even when every retained occurrence
has a different conjugating base or sign. Indices, not row labels,
are used so repeated copies of one rank-height relator are counted
with their true multiplicities. -/
theorem rank_type_lt_of_omitted_index
    {n : ℕ} (s t : Peiffer.Sequence F (RankHeight n))
    (l : List (Fin s.length)) (hl : l.Nodup)
    (hcounts : ∀ j, rankCount t j = rankCount (l.map (fun i => s[i.val])) j)
    (i : Fin s.length) (hi : i ∉ l) :
    descendingCountLT n rankCount t s := by
  classical
  have hsub : List.Subperm l (List.finRange s.length) :=
    hl.subperm (fun x _ => List.mem_finRange x)
  obtain ⟨u,hu,hlsub⟩ := List.subperm_iff.mp hsub
  obtain ⟨r,hr⟩ := hlsub.exists_perm_append
  have hp : List.Perm (List.finRange s.length) (l ++ r) := hu.symm.trans hr
  have hir : i ∈ r := by
    have hm := hp.mem_iff.mp (List.mem_finRange i)
    exact (List.mem_append.mp hm).resolve_left hi
  let get : Fin s.length → Peiffer.Occurrence F (RankHeight n) := fun k => s[k.val]
  have hall : (List.finRange s.length).map get = s := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have hperm : List.Perm s (l.map get ++ r.map get) := by
    have h := hp.map get
    rw [hall,List.map_append] at h
    exact h
  have hsplit (j : ℕ) : rankCount s j =
      rankCount t j + rankCount (r.map get) j := by
    have he := (hperm.filter (fun x => decide (x.1.2.1.val = j))).length_eq
    change rankCount s j = rankCount (l.map get ++ r.map get) j at he
    rw [rankCount_append] at he
    rw [hcounts j]
    exact he
  have hpositive : 0 < rankCount (r.map get) (get i).1.2.1.val := by
    unfold rankCount
    apply List.length_pos_iff_exists_mem.mpr
    refine ⟨get i,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨i,hir,rfl⟩,?_⟩⟩
    simp
  have hlt : descendingCountLT n rankCount t s := by
    apply descending_count_lt_of_pointwise
    · intro j _
      have h := hsplit j
      omega
    · refine ⟨(get i).1.2.1.val,(get i).1.2.1.isLt,?_⟩
      have h := hsplit (get i).1.2.1.val
      omega
  exact hlt

#print axioms rank_type_lt_of_omitted_index

theorem rankMinimal_no_omitted_indices
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (s t : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w s)
    (ht : Peiffer.evaluation (rankHeightRel pick X n) t = w)
    (l : List (Fin s.length)) (hl : l.Nodup)
    (hcounts : ∀ j, rankCount t j = rankCount (l.map (fun i => s[i.val])) j) :
    ∀ i : Fin s.length, i ∈ l := by
  classical
  intro i
  by_contra hi
  have hlt := rank_type_lt_of_omitted_index s t l hl hcounts i hi
  obtain ⟨j,hj,hstrict,habove⟩ := hlt
  exact (Nat.not_lt_of_ge (hs.2 t ht j hj
    (fun k hjk hkn => (habove k hjk hkn).symm))) hstrict

#print axioms rankMinimal_no_omitted_indices



/-- A factor belonging to a nonboundary vertex can be replaced by
a single actual Peiffer occurrence of the original rank and height.
Only the conjugating base is changed, to account for the corner
and for the conjugator supplied by spherical factorization. -/
theorem guba23_vertex_factor_as_occurrence (rows : I → RawWord) (w : F)
    (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (d : DiscDarts (markedRows rows w) (boundaryIdentity s))
    (g : F)
    (hd : discOccurrence (markedRows rows w) (boundaryIdentity s) d ≠
      boundaryOccurrence s) :
    ∃ (j : Fin s.length) (y : Peiffer.Occurrence F I),
      (discOccurrence (markedRows rows w) (boundaryIdentity s) d).val = j.val+1 ∧
      y.1.2 = s[j.val].1.2 ∧
      Peiffer.term (fun i => FreeGroup.mk (rows i)) y =
        g * FreeGroup.mk (((boundaryRibbon rows w s hs).vertexBoundary d).map
          (discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s))) * g⁻¹ := by
  classical
  let P := boundaryRibbon rows w s hs
  let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
  obtain ⟨idx,k,rfl⟩ := exists_discAt (markedRows rows w) (boundaryIdentity s) d
  rw [discOccurrence_at] at hd
  have hpos : 0 < idx.val := by
    by_contra! h
    apply hd
    apply Fin.ext
    change idx.val = 0
    omega
  have hi : idx.val < s.length+1 := by
    simpa [boundaryIdentity] using idx.isLt
  let j : Fin s.length := ⟨idx.val-1,by omega⟩
  have hj : idx.val = j.val+1 := by dsimp [j]; omega
  have hidx : (boundaryIdentity s)[idx] = markOccurrence s[j.val] := by
    have hopt : (boundaryIdentity s)[idx.val]? = some (markOccurrence s[j.val]) := by
      have he := congrArg (fun m : ℕ => (boundaryIdentity s)[m]?) hj
      refine he.trans ?_
      change (s.map markOccurrence)[j.val]? = _
      rw [List.getElem?_map, getElem?_pos s j.val j.isLt]
      rfl
    obtain ⟨h,hread⟩ := List.getElem?_eq_some_iff.mp hopt
    exact hread
  let z := discAt (markedRows rows w) (boundaryIdentity s) idx
    ⟨0,Nat.zero_lt_of_lt k.isLt⟩
  have hcyc : P.rotation.SameCycle z
      (discAt (markedRows rows w) (boundaryIdentity s) idx k) := by
    change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle z _
    rw [disc_sameCycle_iff]
    simp only [z,discOccurrence_at]
  let v : _ → F := fun e => FreeGroup.mk [read e]
  obtain ⟨u,hu⟩ := guba22_cycleProduct_conjugator P.rotation v z _ hcyc
  have hv (e : DiscDarts (markedRows rows w) (boundaryIdentity s)) :
      cycleProduct P.rotation v e = FreeGroup.mk ((P.vertexBoundary e).map read) := by
    change ((P.vertexBoundary e).map v).prod = _
    rw [rawWord_eval_prod,List.map_map]
    rfl
  have hlabel : (boundaryIdentity s)[idx].1.2 = some s[j.val].1.2 := by
    rw [hidx]
    rfl
  have hsign : (boundaryIdentity s)[idx].2 = s[j.val].2 := by
    rw [hidx]
    rfl
  have hz : (P.vertexBoundary z).map read =
      orientedWord (rows s[j.val].1.2) s[j.val].2 := by
    have h := boundaryRibbon_interior_read rows w s hs idx s[j.val].1.2
      hlabel (Nat.zero_lt_of_lt k.isLt)
    exact h.trans (congrArg (orientedWord (rows s[j.val].1.2)) hsign)
  refine ⟨j,((g*u,s[j.val].1.2),s[j.val].2),?_,rfl,?_⟩
  · rw [discOccurrence_at]
    exact hj
  · rw [hv,hv,hz] at hu
    change Peiffer.term (fun i => FreeGroup.mk (rows i))
      ((g*u,s[j.val].1.2),s[j.val].2) =
      g * FreeGroup.mk ((P.vertexBoundary
        (discAt (markedRows rows w) (boundaryIdentity s) idx k)).map read) * g⁻¹
    rw [hu]
    cases h : s[j.val].2
    · simp only [Peiffer.term,Bool.cond_false,orientedWord,← FreeGroup.inv_mk]
      group
    · simp only [Peiffer.term,Bool.cond_true,orientedWord]
      group

#print axioms guba23_vertex_factor_as_occurrence



/-- A nontrivial boundary with a rank-minimal filling has a connected
marked ribbon. Otherwise exact factorization of the marked component
would yield a filling using only a proper subset of the original
occurrence indices, contradicting descending rank minimality. -/
theorem guba23_rankMinimal_ribbon_connected
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s) (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w) :
    (boundaryRibbon (rankHeightRows pick X n) w s hs).Connected := by
  classical
  let rows := rankHeightRows pick X n
  let P := boundaryRibbon rows w s hs
  let z := boundaryDart rows w s hw
  let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
  let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
  let D := {d // P.SameComponent z d}
  let factor : F × D → F := fun t =>
    t.1 * FreeGroup.mk ((P.vertexBoundary t.2.val).map read) * t.1⁻¹
  obtain ⟨l,hl,hsep,_,hprod⟩ :=
    guba23_boundary_component_exact_factors rows w s hs hw
  have build (a : List (F × D))
      (ha : ∀ t ∈ a, idx t.2.val ≠ boundaryOccurrence s)
      (hpair : a.Pairwise (fun t u => idx t.2.val ≠ idx u.2.val)) :
      ∃ (ids : List (Fin s.length)) (t : Peiffer.Sequence F (RankHeight n)),
        ids.Nodup ∧
        (∀ i ∈ ids, ∃ b ∈ a, (idx b.2.val).val = i.val+1) ∧
        (∀ j, rankCount t j = rankCount (ids.map (fun i => s[i.val])) j) ∧
        Peiffer.evaluation (rankHeightRel pick X n) t = (a.map factor).prod := by
    induction a with
    | nil =>
      exact ⟨[],[],by simp,by simp,fun _ => rfl,rfl⟩
    | cons b bs ih =>
      obtain ⟨i,y,hi,hy,hval⟩ := guba23_vertex_factor_as_occurrence rows w s hs
        b.2.val b.1 (ha b List.mem_cons_self)
      obtain ⟨ids,t,hn,hcover,hcount,ht⟩ := ih
        (fun u hu => ha u (List.mem_cons_of_mem _ hu))
        (List.pairwise_cons.mp hpair).2
      refine ⟨i::ids,y::t,?_,?_,?_,?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_,hn⟩
        intro hmem
        obtain ⟨u,hu,he⟩ := hcover i hmem
        exact (List.pairwise_cons.mp hpair).1 u hu (Fin.ext (hi.trans he.symm))
      · intro j hj
        rcases List.mem_cons.mp hj with h | h
        · subst j
          exact ⟨b,List.mem_cons_self,hi⟩
        · obtain ⟨u,hu,he⟩ := hcover j h
          exact ⟨u,List.mem_cons_of_mem _ hu,he⟩
      · intro j
        change rankCount ([y] ++ t) j =
          rankCount ([s[i.val]] ++ ids.map (fun i => s[i.val])) j
        simp only [rankCount_append,rankCount_singleton,hy,hcount]
      · have hval' : Peiffer.term (rankHeightRel pick X n) y = factor b := by
          simpa only [rows,rankHeightRows_eval] using hval
        change Peiffer.term (rankHeightRel pick X n) y *
          Peiffer.evaluation (rankHeightRel pick X n) t =
            factor b * (bs.map factor).prod
        rw [hval',ht]
  obtain ⟨ids,t,hn,hcover,hcount,ht⟩ := build l hl hsep
  have hall := rankMinimal_no_omitted_indices pick X n w s t hm
    (ht.trans hprod) ids hn hcount
  have hconn (d : DiscDarts (markedRows rows w) (boundaryIdentity s)) :
      P.SameComponent z d := by
    by_cases h : idx d = boundaryOccurrence s
    · exact P.component_of_vertexCycle ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr h)
    · obtain ⟨i,y,hi,_,_⟩ := guba23_vertex_factor_as_occurrence rows w s hs d 1 h
      obtain ⟨b,_,hb⟩ := hcover i (hall i)
      have hcycle : P.rotation.SameCycle b.2.val d := by
        change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle b.2.val d
        rw [disc_sameCycle_iff]
        exact Fin.ext (hb.trans hi.symm)
      exact Relation.EqvGen.trans _ _ _ b.2.property (P.component_of_vertexCycle hcycle)
  intro d e
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (hconn d)) (hconn e)

#print axioms guba23_rankMinimal_ribbon_connected



/-! ### The two-boundary deletion package

Collect the geometric and algebraic outputs of deleting a specified
cell into one theorem. The underlying capped annular ribbon is the
original spherical ribbon, with two distinguished vertex discs.
The remaining rank profile is strictly smaller and is minimal even
against competing based fillings with a different connecting path.
No claim about Guba's regularity or preferred bands is implicit.
-/

theorem guba23_delete_cell_two_boundary_package
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p r : Peiffer.Sequence F (RankHeight n))
    (x : Peiffer.Occurrence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w (p ++ [x] ++ r))
    (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) (p ++ [x] ++ r) = w) :
    let s := p ++ [x] ++ r
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let rel := rankHeightRel pick X n
    P.Connected ∧ P.EulerEquality ∧
      (P.vertexBoundary z).map read = FreeGroup.invRev w.toWord ∧
      (∃ d : DiscDarts (markedRows rows w) (boundaryIdentity s),
        P.SameComponent z d ∧ ¬ P.rotation.SameCycle z d ∧
        (P.vertexBoundary d).map read = orientedWord (rows x.1.2) x.2 ∧
        (∀ e, P.rotation.SameCycle d e ↔
          (discOccurrence (markedRows rows w) (boundaryIdentity s) e).val = p.length+1)) ∧
      descendingCountLT n rankCount (p ++ r) s ∧
      (∀ g t, Peiffer.evaluation rel ([shiftOccurrence g x] ++ t) = w →
        ¬ descendingCountLT n rankCount t (p ++ r)) := by
  intro s rows P z read rel
  have hc : P.Connected :=
    guba23_rankMinimal_ribbon_connected pick X n w s hm hw hs
  obtain ⟨d,_,hne,hread,hidx⟩ :=
    guba23_designated_boundary_cycle pick X n w p r x hm hw hs
  refine ⟨hc,boundaryRibbon_euler rows w s hs,
    boundaryRibbon_read rows w s hs hw,⟨d,hc z d,hne,hread,hidx⟩,?_,?_⟩
  · exact rank_type_lt_of_omitted_occurrence p r x (p ++ r) (List.Sublist.refl _)
  · intro g t ht
    exact guba23_delete_cell_variable_base_minimal pick X n w p r x hm g t ht

#print axioms guba23_delete_cell_two_boundary_package



/-! ### Induction on genuine subfillings

A contiguous subexpression in any rank-minimal filling is itself
rank-minimal for its own evaluation. If it omits even one occurrence,
its type strictly decreases. The boundary word need not coincide
with the parent boundary. This is the algebraic substitution rule
needed for cuts in Lemmas 21--23; realizing a particular geometric
cut by such an expression remains a separate obligation.
-/

theorem rankMinimal_subfilling_minimal
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p b r : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ b ++ r)) :
    RankMinimalExpression pick X n
      (Peiffer.evaluation (rankHeightRel pick X n) b) b := by
  refine ⟨rfl,?_⟩
  intro t ht j hj habove
  by_contra! h
  exact rankMinimal_block_no_reduction pick X n w p b r t hs ht.symm
    j hj habove h

/-- Type comparison is independent of the number of lower-rank cells
introduced by a replacement. In particular smaller-type induction
can be applied to a proper block of an expression, without fixing
its evaluation or the boundary of the parent diagram. -/
theorem rankMinimal_proper_subfilling
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (p b r : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w (p ++ b ++ r))
    (hproper : p ≠ [] ∨ r ≠ []) :
    RankMinimalExpression pick X n
      (Peiffer.evaluation (rankHeightRel pick X n) b) b ∧
      descendingCountLT n rankCount b (p ++ b ++ r) := by
  refine ⟨rankMinimal_subfilling_minimal pick X n w p b r hs,?_⟩
  apply descending_count_lt_of_pointwise
  · intro j _
    simp only [rankCount_append]
    omega
  · have hex : ∃ x : Peiffer.Occurrence F (RankHeight n), x ∈ p ∨ x ∈ r := by
      rcases hproper with hp | hr
      · obtain ⟨x,hx⟩ := List.length_pos_iff_exists_mem.mp
          (List.length_pos_iff.mpr hp)
        exact ⟨x,Or.inl hx⟩
      · obtain ⟨x,hx⟩ := List.length_pos_iff_exists_mem.mp
          (List.length_pos_iff.mpr hr)
        exact ⟨x,Or.inr hx⟩
    obtain ⟨x,hx⟩ := hex
    refine ⟨x.1.2.1.val,x.1.2.1.isLt,?_⟩
    have hpos (a : Peiffer.Sequence F (RankHeight n)) (ha : x ∈ a) :
        0 < rankCount a x.1.2.1.val := by
      unfold rankCount
      apply List.length_pos_iff_exists_mem.mpr
      exact ⟨x,List.mem_filter.mpr ⟨ha,by simp⟩⟩
    simp only [rankCount_append]
    rcases hx with hx | hx
    · have hp := hpos p hx
      omega
    · have hr := hpos r hx
      omega

/-- Rank-profile-preserving Peiffer regrouping transports minimality.
A geometric cut need only exhibit a based factorization with the
same counts at all ranks, rather than equality of ordered lists. -/
theorem rankMinimal_transport_profile
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (s t : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w s)
    (ht : Peiffer.evaluation (rankHeightRel pick X n) t = w)
    (hc : ∀ j, rankCount s j = rankCount t j) :
    RankMinimalExpression pick X n w t := by
  refine ⟨ht,?_⟩
  intro u hu j hj habove
  rw [← hc j]
  exact hs.2 u hu j hj (fun k hjk hkn => (hc k).trans (habove k hjk hkn))

/-- The exact interface for induction on a proper geometric region:
regroup the parent expression without changing its rank profile;
then the isolated block is minimal and has strictly smaller type
than the original parent, regardless of its new boundary value. -/
theorem guba23_regrouped_region_induction
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F)
    (s p b r : Peiffer.Sequence F (RankHeight n))
    (hs : RankMinimalExpression pick X n w s)
    (ht : Peiffer.evaluation (rankHeightRel pick X n) (p ++ b ++ r) = w)
    (hc : ∀ j, rankCount s j = rankCount (p ++ b ++ r) j)
    (hproper : p ≠ [] ∨ r ≠ []) :
    RankMinimalExpression pick X n
      (Peiffer.evaluation (rankHeightRel pick X n) b) b ∧
      descendingCountLT n rankCount b s := by
  obtain ⟨hm,j,hj,hlt,habove⟩ := rankMinimal_proper_subfilling
    pick X n w p b r (rankMinimal_transport_profile pick X n w s
      (p ++ b ++ r) hs ht hc) hproper
  refine ⟨hm,j,hj,?_,?_⟩
  · rw [hc j]
    exact hlt
  · intro k hjk hkn
    rw [hc k]
    exact habove k hjk hkn

#print axioms rankMinimal_subfilling_minimal
#print axioms rankMinimal_proper_subfilling
#print axioms rankMinimal_transport_profile
#print axioms guba23_regrouped_region_induction



/-- Exact filling of an actual cut component with one peripheral
cycle and otherwise intact original cells. Unlike the normal-closure
version of the boundary theorem, this records distinct original cell
indices, and represents the literal inverse boundary reading by
exactly those cells. The hypothesis is local to this component:
other components may have arbitrary split vertices. -/
theorem guba23_refined_component_exact_occurrences
    (rows : I → RawWord) (w : F) (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (tau : Equiv.Perm (DiscDarts (markedRows rows w) (boundaryIdentity s))) :
    let P := boundaryRibbon rows w s hs
    let Q := P.withRotation tau
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
    ∀ a, SplitRefinement P.rotation tau →
      (∀ d, Q.SameComponent a d → ¬ tau.SameCycle a d →
        idx d ≠ boundaryOccurrence s ∧
        Q.vertexBoundary d = P.vertexBoundary d) →
      ∃ l : List (Fin s.length × Peiffer.Occurrence F I),
        (l.map Prod.fst).Nodup ∧
        (∀ t ∈ l, t.2.1.2 = s[t.1.val].1.2 ∧
          ∃ d, Q.SameComponent a d ∧ ¬ tau.SameCycle a d ∧
            (idx d).val = t.1.val+1) ∧
        (∀ d, Q.SameComponent a d → ¬ tau.SameCycle a d →
          ∃ t ∈ l, (idx d).val = t.1.val+1) ∧
        Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) (l.map Prod.snd) =
          (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹ := by
  classical
  intro P Q read idx a href hint
  let C := Q.componentRibbon a
  let D := {d // Q.SameComponent a d}
  let z : D := ⟨a,Relation.EqvGen.refl a⟩
  let v : D → F := fun d => FreeGroup.mk [read d.val]
  have he : ∀ d, v (C.edge d) = (v d)⁻¹ := by
    intro d
    change FreeGroup.mk [read (P.edge d.val)] = (FreeGroup.mk [read d.val])⁻¹
    have hread : read (P.edge d.val) = reverseLetter (read d.val) :=
      relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
        (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs) d.val
    rw [hread]
    exact signedLetterValue_reverse _
  have hEQ : Q.EulerEquality :=
    P.splitRefinement_preserves_euler href (boundaryRibbon_euler rows w s hs)
  have hEC : C.EulerEquality := by
    change Fintype.card C.Vertex + Fintype.card C.Face =
      Fintype.card C.Edge + 2 * Fintype.card C.Component
    rw [Q.componentRibbon_card_components,mul_one]
    exact Q.componentRibbon_sphere hEQ a
  have same (d e : D) : C.rotation.SameCycle d e ↔ tau.SameCycle d.val e.val :=
    Q.restrict_sameVertex_iff (Q.SameComponent a)
      (Q.component_membership_edge a) (Q.component_membership_rotation a) d e
  have hv (d : D) : cycleProduct C.rotation v d =
      FreeGroup.mk ((Q.vertexBoundary d.val).map read) := by
    change ((C.vertexBoundary d).map v).prod = _
    rw [← component_vertex_read Q read a d,rawWord_eval_prod,List.map_map]
    rfl
  obtain ⟨f,hf,hsep,hcov,hprod⟩ := guba23_component_exact_vertex_product
    C v he (Q.componentRibbon_connected a) hEC z
  let value : F × D → F := fun t =>
    t.1 * FreeGroup.mk ((Q.vertexBoundary t.2.val).map read) * t.1⁻¹
  have localHint (d : D) (hd : ¬ C.rotation.SameCycle z d) :
      idx d.val ≠ boundaryOccurrence s ∧ Q.vertexBoundary d.val = P.vertexBoundary d.val :=
    hint d.val d.property (fun h => hd ((same z d).mpr h))
  have build (b : List (F × D))
      (hb : ∀ t ∈ b, ¬ C.rotation.SameCycle z t.2)
      (hp : b.Pairwise (fun t u => ¬ C.rotation.SameCycle t.2 u.2)) :
      ∃ l : List (Fin s.length × Peiffer.Occurrence F I),
        (l.map Prod.fst).Nodup ∧
        (∀ t ∈ l, t.2.1.2 = s[t.1.val].1.2 ∧
          ∃ u ∈ b, (idx u.2.val).val = t.1.val+1) ∧
        (∀ u ∈ b, ∃ t ∈ l, (idx u.2.val).val = t.1.val+1) ∧
        Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) (l.map Prod.snd) =
          (b.map value).prod := by
    induction b with
    | nil => exact ⟨[],by simp,by simp,by simp,rfl⟩
    | cons u us ih =>
      obtain ⟨hidx,hread⟩ := localHint u.2 (hb u List.mem_cons_self)
      obtain ⟨i,y,hi,hy,hval⟩ := guba23_vertex_factor_as_occurrence
        rows w s hs u.2.val u.1 hidx
      obtain ⟨l,hn,hcover,hsurj,hl⟩ := ih
        (fun t ht => hb t (List.mem_cons_of_mem _ ht)) (List.pairwise_cons.mp hp).2
      refine ⟨(i,y)::l,?_,?_,?_,?_⟩
      · simp only [List.map_cons,List.nodup_cons]
        refine ⟨?_,hn⟩
        intro hmem
        obtain ⟨t,ht,htidx⟩ := List.mem_map.mp hmem
        obtain ⟨q,hq,hqi⟩ := (hcover t ht).2
        have hsame : P.rotation.SameCycle u.2.val q.2.val := by
          change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle
            u.2.val q.2.val
          rw [disc_sameCycle_iff]
          apply Fin.ext
          rw [hi,hqi,htidx]
        have hsame' : tau.SameCycle u.2.val q.2.val :=
          (sameCycle_iff_of_vertexBoundary_eq P Q u.2.val q.2.val hread).mpr hsame
        exact (List.pairwise_cons.mp hp).1 q hq ((same u.2 q.2).mpr hsame')
      · intro t ht
        rcases List.mem_cons.mp ht with ht | ht
        · subst t
          exact ⟨hy,u,List.mem_cons_self,hi⟩
        · obtain ⟨hlabel,q,hq,hqi⟩ := hcover t ht
          exact ⟨hlabel,q,List.mem_cons_of_mem _ hq,hqi⟩
      · intro t ht
        rcases List.mem_cons.mp ht with ht | ht
        · subst t
          exact ⟨(i,y),List.mem_cons_self,hi⟩
        · obtain ⟨q,hq,hqi⟩ := hsurj t ht
          exact ⟨q,List.mem_cons_of_mem _ hq,hqi⟩
      · change Peiffer.term (fun i => FreeGroup.mk (rows i)) y *
          Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) (l.map Prod.snd) =
          value u * (us.map value).prod
        rw [hl]
        have hval' : Peiffer.term (fun i => FreeGroup.mk (rows i)) y = value u := by
          change _ = u.1 * FreeGroup.mk ((Q.vertexBoundary u.2.val).map read) * u.1⁻¹
          rw [hread]
          exact hval
        rw [hval']
  obtain ⟨l,hn,hcover,hsurj,hl⟩ := build f hf hsep
  refine ⟨l,hn,?_,?_,?_⟩
  · intro t ht
    obtain ⟨hlabel,u,hu,hi⟩ := hcover t ht
    exact ⟨hlabel,u.2.val,u.2.property,fun h => hf u hu ((same z u.2).mpr h),hi⟩
  · intro d hd hn'
    let e : D := ⟨d,hd⟩
    obtain ⟨u,hu,hue⟩ := hcov e (fun h => hn' ((same z e).mp h))
    obtain ⟨t,ht,hi⟩ := hsurj u hu
    have heq : idx u.2.val = idx d := by
      have hread := (localHint u.2 (hf u hu)).2
      have hcyc := (sameCycle_iff_of_vertexBoundary_eq P Q u.2.val d hread).mp
        ((same u.2 e).mp hue)
      exact (disc_sameCycle_iff _ _ _ _).mp hcyc
    exact ⟨t,ht,(congrArg Fin.val heq).symm.trans hi⟩
  · rw [hl]
    simp only [hv] at hprod
    change FreeGroup.mk ((Q.vertexBoundary a).map read) * (f.map value).prod = 1 at hprod
    calc
      _ = (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹ *
          (FreeGroup.mk ((Q.vertexBoundary a).map read) * (f.map value).prod) := by group
      _ = _ := by rw [hprod,mul_one]

#print axioms guba23_refined_component_exact_occurrences



/-- Transitivity of the graded order follows by comparing the
highest differing ranks. No assumption on lower-rank counts. -/
theorem descending_count_trans {A : Type} (n : ℕ) (count : A → ℕ → ℕ)
    {u t s : A} (hut : descendingCountLT n count u t)
    (hts : descendingCountLT n count t s) :
    descendingCountLT n count u s := by
  obtain ⟨i,hi,hu,huabove⟩ := hut
  obtain ⟨j,hj,ht,htabove⟩ := hts
  rcases lt_trichotomy i j with hij | hij | hji
  · refine ⟨j,hj,?_,?_⟩
    · rw [huabove j hij hj]
      exact ht
    · intro k hk hkn
      exact (huabove k (lt_trans hij hk) hkn).trans (htabove k hk hkn)
  · subst j
    exact ⟨i,hi,lt_trans hu ht,fun k hk hkn =>
      (huabove k hk hkn).trans (htabove k hk hkn)⟩
  · refine ⟨i,hi,?_,?_⟩
    · rw [← htabove i hji hi]
      exact hu
    · intro k hk hkn
      exact (huabove k hk hkn).trans (htabove k (lt_trans hji hk) hkn)

/-- A genuine smaller-type filling can always be replaced by a
rank-minimal filling of the same boundary, still below the parent
type. This does not assert that the geometric region itself was
minimal, and hence only permits induction on its boundary value. -/
theorem rankMinimal_exists_below_type
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s t : Peiffer.Sequence F (RankHeight n))
    (ht : Peiffer.evaluation (rankHeightRel pick X n) t = w)
    (hlt : descendingCountLT n rankCount t s) :
    ∃ u : Peiffer.Sequence F (RankHeight n),
      RankMinimalExpression pick X n w u ∧ descendingCountLT n rankCount u s := by
  obtain ⟨u,hu,hmin⟩ := exists_descending_count_min n
    (fun v : Peiffer.Sequence F (RankHeight n) =>
      Peiffer.evaluation (rankHeightRel pick X n) v = w ∧
        descendingCountLT n rankCount v s)
    rankCount ⟨t,ht,hlt⟩
  refine ⟨u,⟨hu.1,?_⟩,hu.2⟩
  intro v hv j hj habove
  by_contra! h
  have hvu : descendingCountLT n rankCount v u :=
    ⟨j,hj,h,fun k hk hkn => (habove k hk hkn).symm⟩
  exact (Nat.not_lt_of_ge (hmin v
    ⟨hv,descending_count_trans n rankCount hvu hu.2⟩ j hj habove)) h

/-- A cut component omitting one original cell index admits an
actual rank-minimal filling of its literal boundary, of strictly
smaller type than the parent. This is the boundary-value induction
interface; conclusions about the geometry of the original region
still require a separate substitution argument. -/
theorem guba21_cut_boundary_smaller_type
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (tau : Equiv.Perm (DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s))) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let Q := P.withRotation tau
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
    ∀ a, SplitRefinement P.rotation tau →
      (∀ d, Q.SameComponent a d → ¬ tau.SameCycle a d →
        idx d ≠ boundaryOccurrence s ∧
        Q.vertexBoundary d = P.vertexBoundary d) →
      (∃ i : Fin s.length, ∀ d, Q.SameComponent a d → ¬ tau.SameCycle a d →
        (idx d).val ≠ i.val+1) →
      ∃ u : Peiffer.Sequence F (RankHeight n),
        RankMinimalExpression pick X n
          (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹ u ∧
        descendingCountLT n rankCount u s := by
  classical
  intro rows P Q read idx a href hint homit
  obtain ⟨i,hi⟩ := homit
  obtain ⟨l,hn,hlabels,_,heval⟩ :=
    guba23_refined_component_exact_occurrences rows w s hs tau a href hint
  have hnot : i ∉ l.map Prod.fst := by
    intro hm
    obtain ⟨x,hx,hxi⟩ := List.mem_map.mp hm
    obtain ⟨_,d,hd,hd',hdi⟩ := hlabels x hx
    exact hi d hd hd' (hdi.trans (congrArg (fun k : Fin s.length => k.val+1) hxi))
  have counts (b : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)))
      (hb : ∀ x ∈ b, x.2.1.2 = s[x.1.val].1.2) :
      ∀ j, rankCount (b.map Prod.snd) j =
        rankCount ((b.map Prod.fst).map (fun k => s[k.val])) j := by
    induction b with
    | nil => intro j; rfl
    | cons x xs ih =>
      intro j
      change rankCount ([x.2] ++ xs.map Prod.snd) j =
        rankCount ([s[x.1.val]] ++ (xs.map Prod.fst).map (fun k => s[k.val])) j
      simp only [rankCount_append,rankCount_singleton,hb x List.mem_cons_self,
        ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) j]
  have hlt := rank_type_lt_of_omitted_index s (l.map Prod.snd)
    (l.map Prod.fst) hn (counts l (fun x hx => (hlabels x hx).1)) i hnot
  apply rankMinimal_exists_below_type pick X n _ s (l.map Prod.snd) _ hlt
  simpa only [rows,rankHeightRows_eval] using heval

#print axioms descending_count_trans
#print axioms rankMinimal_exists_below_type
#print axioms guba21_cut_boundary_smaller_type



/-- Rank counts of an indexed filling depend only on the original
indices when every relator label is preserved. -/
theorem indexed_rankCount_eq {n : ℕ}
    (s : Peiffer.Sequence F (RankHeight n))
    (l : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)))
    (hl : ∀ x ∈ l, x.2.1.2 = s[x.1.val].1.2) (j : ℕ) :
    rankCount (l.map Prod.snd) j =
      rankCount ((l.map Prod.fst).map (fun i => s[i.val])) j := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change rankCount ([x.2] ++ xs.map Prod.snd) j =
      rankCount ([s[x.1.val]] ++ (xs.map Prod.fst).map (fun i => s[i.val])) j
    simp only [rankCount_append,rankCount_singleton,hl x List.mem_cons_self,
      ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))]

/-- An indexed filling of the original boundary using distinct
original indices is itself rank-minimal, with exactly the original
rank profile. No hypothesis of surjectivity on indices is required:
minimality forces it. -/
theorem rankMinimal_indexed_reassembly
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s)
    (l : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)))
    (hn : (l.map Prod.fst).Nodup)
    (hl : ∀ x ∈ l, x.2.1.2 = s[x.1.val].1.2)
    (he : Peiffer.evaluation (rankHeightRel pick X n) (l.map Prod.snd) = w) :
    RankMinimalExpression pick X n w (l.map Prod.snd) ∧
      (∀ j, rankCount s j = rankCount (l.map Prod.snd) j) := by
  classical
  have hall := rankMinimal_no_omitted_indices pick X n w s (l.map Prod.snd)
    hm he (l.map Prod.fst) hn (indexed_rankCount_eq s l hl)
  have hfin : (List.finRange s.length).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hp : List.Perm (List.finRange s.length) (l.map Prod.fst) :=
    (List.perm_ext_iff_of_nodup hfin hn).mpr
      (fun i => ⟨fun _ => hall i,fun _ => List.mem_finRange i⟩)
  let get : Fin s.length → Peiffer.Occurrence F (RankHeight n) := fun i => s[i.val]
  have hget : (List.finRange s.length).map get = s := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have hperm : List.Perm s ((l.map Prod.fst).map get) := by
    have h := hp.map get
    rw [hget] at h
    exact h
  have hc (j : ℕ) : rankCount s j = rankCount (l.map Prod.snd) j := by
    rw [indexed_rankCount_eq s l hl j]
    exact (hperm.filter (fun x => decide (x.1.2.1.val = j))).length_eq
  exact ⟨rankMinimal_transport_profile pick X n w s _ hm he hc,hc⟩

/-- Exact reassembly for a separating cut of the outer boundary.
Both actual components, not just new fillings of their boundary
values, have rank-minimal indexed expressions. The only interior
vertices allowed in either component are intact original relators.
The peripheral words concatenate in the original based order. -/
theorem guba21_separating_boundary_cut_minimal
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s) (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (tau : Equiv.Perm (DiscDarts (markedRows (rankHeightRows pick X n) w)
      (boundaryIdentity s))) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let Q := P.withRotation tau
    let a := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
    ∀ b, SplitRefinement P.rotation tau →
      ¬ Q.SameComponent a b →
      P.vertexBoundary a = Q.vertexBoundary a ++ Q.vertexBoundary b →
      (∀ c ∈ [a,b], ∀ d, Q.SameComponent c d → ¬ tau.SameCycle c d →
        idx d ≠ boundaryOccurrence s ∧ Q.vertexBoundary d = P.vertexBoundary d) →
      ∃ l r : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)),
        ((l ++ r).map Prod.fst).Nodup ∧
        (∀ t ∈ l, t.2.1.2 = s[t.1.val].1.2 ∧
          ∃ d, Q.SameComponent a d ∧ ¬ tau.SameCycle a d ∧
            (idx d).val = t.1.val+1) ∧
        (∀ t ∈ r, t.2.1.2 = s[t.1.val].1.2 ∧
          ∃ d, Q.SameComponent b d ∧ ¬ tau.SameCycle b d ∧
            (idx d).val = t.1.val+1) ∧
        (∀ d, Q.SameComponent a d → ¬ tau.SameCycle a d →
          ∃ t ∈ l, (idx d).val = t.1.val+1) ∧
        (∀ d, Q.SameComponent b d → ¬ tau.SameCycle b d →
          ∃ t ∈ r, (idx d).val = t.1.val+1) ∧
        RankMinimalExpression pick X n
          (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹ (l.map Prod.snd) ∧
        RankMinimalExpression pick X n
          (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹ (r.map Prod.snd) ∧
        (∀ j, rankCount s j = rankCount (l.map Prod.snd) j +
          rankCount (r.map Prod.snd) j) := by
  classical
  intro rows P Q a read idx b href hsep hsplit hint
  obtain ⟨l,hl,hla,hlc,hle⟩ :=
    guba23_refined_component_exact_occurrences rows w s hs tau a href
      (hint a (by simp))
  obtain ⟨r,hr,hrb,hrc,hre⟩ :=
    guba23_refined_component_exact_occurrences rows w s hs tau b href
      (hint b (by simp))
  have hdis (x : Fin s.length) (hx : x ∈ l.map Prod.fst) :
      x ∉ r.map Prod.fst := by
    intro hy
    obtain ⟨u,hu,hux⟩ := List.mem_map.mp hx
    obtain ⟨v,hv,hvx⟩ := List.mem_map.mp hy
    obtain ⟨_,d,hd,hda,hdi⟩ := hla u hu
    obtain ⟨_,e,he,heb,hei⟩ := hrb v hv
    have hde : idx d = idx e := by
      apply Fin.ext
      rw [hdi,hei,hux,hvx]
    have hcyc : P.rotation.SameCycle d e :=
      (disc_sameCycle_iff _ _ _ _).mpr hde
    have hcyc' : Q.rotation.SameCycle d e :=
      (sameCycle_iff_of_vertexBoundary_eq P Q d e
        (hint a (by simp) d hd hda).2).mpr hcyc
    exact hsep (Relation.EqvGen.trans _ _ _ hd
      (Relation.EqvGen.trans _ _ _ (Q.component_of_vertexCycle hcyc')
        (Relation.EqvGen.symm _ _ he)))
  have hn : ((l ++ r).map Prod.fst).Nodup := by
    rw [List.map_append,List.nodup_append]
    exact ⟨hl,hr,fun x hx y hy h => hdis x hx (h ▸ hy)⟩
  have hn' : ((r ++ l).map Prod.fst).Nodup := by
    rw [List.map_append,List.nodup_append]
    exact ⟨hr,hl,fun x hx y hy h => hdis y hy (h ▸ hx)⟩
  have hlabel (x : Fin s.length × Peiffer.Occurrence F (RankHeight n))
      (hx : x ∈ r ++ l) : x.2.1.2 = s[x.1.val].1.2 := by
    rcases List.mem_append.mp hx with hx | hx
    · exact (hrb x hx).1
    · exact (hla x hx).1
  have hle' : Peiffer.evaluation (rankHeightRel pick X n) (l.map Prod.snd) =
      (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹ := by
    simpa only [rows,rankHeightRows_eval] using hle
  have hre' : Peiffer.evaluation (rankHeightRel pick X n) (r.map Prod.snd) =
      (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹ := by
    simpa only [rows,rankHeightRows_eval] using hre
  have hw' : FreeGroup.mk ((Q.vertexBoundary a).map read) *
      FreeGroup.mk ((Q.vertexBoundary b).map read) = w⁻¹ := by
    rw [FreeGroup.mul_mk,← List.map_append,← hsplit]
    rw [boundaryRibbon_read rows w s hs hw,← FreeGroup.inv_mk,FreeGroup.mk_toWord]
  have heval : Peiffer.evaluation (rankHeightRel pick X n) ((r ++ l).map Prod.snd) = w := by
    rw [List.map_append,peiffer_evaluation_append,hre',hle',← mul_inv_rev,hw',inv_inv]
  obtain ⟨hmin,hcount⟩ := rankMinimal_indexed_reassembly pick X n w s hm
    (r ++ l) hn' hlabel heval
  rw [List.map_append] at hmin
  have hminL := rankMinimal_subfilling_minimal pick X n w
    (r.map Prod.snd) (l.map Prod.snd) [] (by simpa using hmin)
  have hminR := rankMinimal_subfilling_minimal pick X n w
    [] (r.map Prod.snd) (l.map Prod.snd) (by simpa using hmin)
  rw [hle'] at hminL
  rw [hre'] at hminR
  refine ⟨l,r,hn,hla,hrb,hlc,hrc,hminL,hminR,?_⟩
  intro j
  rw [hcount j,List.map_append,rankCount_append,Nat.add_comm]

#print axioms indexed_rankCount_eq
#print axioms rankMinimal_indexed_reassembly
#print axioms guba21_separating_boundary_cut_minimal



/-- A separating single cut of one vertex cannot alter any interior
vertex of either component. The two new peripheral cycles are the
only pieces of the old vertex. -/
theorem separating_vertexCut_intact {D : Type} [Fintype D]
    (P : RibbonMap D) (a b : D) (hne : a ≠ b)
    (hsame : P.rotation.SameCycle a b) :
    let Q := P.vertexCut a b
    ¬ Q.SameComponent a b →
    ∀ c ∈ [a,b], ∀ d, Q.SameComponent c d →
      ¬ Q.rotation.SameCycle c d →
      ¬ P.rotation.SameCycle a d ∧
        Q.vertexBoundary d = P.vertexBoundary d := by
  intro Q hsep c hc d hcd hnot
  have hpart := vertexCut_partition P a b hne hsame
  have hold : ¬ P.rotation.SameCycle a d := by
    intro hh
    have hd := (P.mem_vertexBoundary_iff a d).mpr hh
    rw [hpart,List.mem_append] at hd
    have hc' : c = a ∨ c = b := by simpa using hc
    rcases hc' with hca | hcb
    · subst c
      rcases hd with hd | hd
      · exact hnot ((Q.mem_vertexBoundary_iff a d).mp hd)
      · have hbd := Q.component_of_vertexCycle
          ((Q.mem_vertexBoundary_iff b d).mp hd)
        exact hsep (Relation.EqvGen.trans _ _ _ hcd
          (Relation.EqvGen.symm _ _ hbd))
    · subst c
      rcases hd with hd | hd
      · have had := Q.component_of_vertexCycle
          ((Q.mem_vertexBoundary_iff a d).mp hd)
        exact hsep (Relation.EqvGen.trans _ _ _ had
          (Relation.EqvGen.symm _ _ hcd))
      · exact hnot ((Q.mem_vertexBoundary_iff b d).mp hd)
  exact ⟨hold,vertexCut_other_vertex_read P a b d
    (fun h => hold h.symm) (fun h => hold (hsame.trans h.symm))⟩

/-- If a rank profile is the sum of two nonempty fillings, both
fillings have strictly smaller descending type than the parent. -/
theorem guba21_separating_profiles_strict {n : ℕ}
    (s l r : Peiffer.Sequence F (RankHeight n))
    (hl : l ≠ []) (hr : r ≠ [])
    (hc : ∀ j, rankCount s j = rankCount l j + rankCount r j) :
    descendingCountLT n rankCount l s ∧
    descendingCountLT n rankCount r s := by
  have pos (t : Peiffer.Sequence F (RankHeight n)) (ht : t ≠ []) :
      ∃ j < n, 0 < rankCount t j := by
    obtain ⟨x,hx⟩ := List.length_pos_iff_exists_mem.mp
      (List.length_pos_iff.mpr ht)
    refine ⟨x.1.2.1.val,x.1.2.1.isLt,?_⟩
    unfold rankCount
    apply List.length_pos_iff_exists_mem.mpr
    exact ⟨x,List.mem_filter.mpr ⟨hx,by simp⟩⟩
  obtain ⟨i,hi,hli⟩ := pos l hl
  obtain ⟨j,hj,hrj⟩ := pos r hr
  constructor
  · apply descending_count_lt_of_pointwise
    · intro k _
      rw [hc k]
      omega
    · exact ⟨j,hj,by rw [hc j]; omega⟩
  · apply descending_count_lt_of_pointwise
    · intro k _
      rw [hc k]
      omega
    · exact ⟨i,hi,by rw [hc i]; omega⟩

/-- An actual separating cut of the outer vertex yields minimal
fillings of the two literal boundary values. If both values are
nonidentity, both fillings have strictly smaller type. The
refinement, exact partition and intact-cell hypotheses of the
general reassembly theorem are derived from the single cut. -/
theorem guba21_actual_separating_cut_induction
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s) (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∀ b, a ≠ b → P.rotation.SameCycle a b →
      let Q := P.vertexCut a b
      ¬ Q.SameComponent a b →
      let u := (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹
      let v := (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹
      u ≠ 1 → v ≠ 1 →
      ∃ l r : Peiffer.Sequence F (RankHeight n),
        RankMinimalExpression pick X n u l ∧
        RankMinimalExpression pick X n v r ∧
        (∀ j, rankCount s j = rankCount l j + rankCount r j) ∧
        descendingCountLT n rankCount l s ∧
        descendingCountLT n rankCount r s := by
  classical
  intro rows P a read b hne hsame Q hsep u v hu hv
  let tau := Q.rotation
  have hQ : P.withRotation tau = Q := by
    apply RibbonMap.ext <;> rfl
  have href : SplitRefinement P.rotation tau :=
    SplitRefinement.single P.rotation a b hne hsame
  have hpart : P.vertexBoundary a =
      (P.withRotation tau).vertexBoundary a ++
        (P.withRotation tau).vertexBoundary b := by
    rw [hQ]
    exact vertexCut_partition P a b hne hsame
  have hint : ∀ c ∈ [a,b], ∀ d, (P.withRotation tau).SameComponent c d →
      ¬ tau.SameCycle c d →
      discOccurrence (markedRows rows w) (boundaryIdentity s) d ≠
        boundaryOccurrence s ∧
        (P.withRotation tau).vertexBoundary d = P.vertexBoundary d := by
    intro c hc d hcd hnot
    rw [hQ] at hcd ⊢
    obtain ⟨hold,hread⟩ := separating_vertexCut_intact P a b hne hsame
      hsep c hc d hcd hnot
    refine ⟨?_,hread⟩
    intro he
    exact hold ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr he)
  have hsep' : ¬ (P.withRotation tau).SameComponent a b := by
    rw [hQ]
    exact hsep
  obtain ⟨l,r,_,_,_,_,_,hl,hr,hcount⟩ :=
    guba21_separating_boundary_cut_minimal pick X n w s hm hw hs tau
      b href hsep' hpart hint
  change RankMinimalExpression pick X n
    (FreeGroup.mk (((P.withRotation tau).vertexBoundary a).map read))⁻¹
      (l.map Prod.snd) at hl
  change RankMinimalExpression pick X n
    (FreeGroup.mk (((P.withRotation tau).vertexBoundary b).map read))⁻¹
      (r.map Prod.snd) at hr
  rw [hQ] at hl hr
  have hln : l.map Prod.snd ≠ [] := by
    intro he
    apply hu
    have h := hl.1
    rw [he] at h
    exact h.symm
  have hrn : r.map Prod.snd ≠ [] := by
    intro he
    apply hv
    have h := hr.1
    rw [he] at h
    exact h.symm
  obtain ⟨hlt,hrt⟩ := guba21_separating_profiles_strict s
    (l.map Prod.snd) (r.map Prod.snd) hln hrn hcount
  exact ⟨l.map Prod.snd,r.map Prod.snd,hl,hr,hcount,hlt,hrt⟩

#print axioms separating_vertexCut_intact
#print axioms guba21_separating_profiles_strict
#print axioms guba21_actual_separating_cut_induction


/-- A literal split of a canonical free-group word has no hidden
cancellation in either part or across the split. Derive this from
Mathlib's norm inequalities, without a second reduction algorithm. -/
theorem canonical_split_norm (z : F) (L R : RawWord)
    (h : L ++ R = z.toWord) :
    FreeGroup.norm (FreeGroup.mk L) = L.length ∧
    FreeGroup.norm (FreeGroup.mk R) = R.length := by
  have hprod : FreeGroup.mk L * FreeGroup.mk R = z := by
    rw [FreeGroup.mul_mk,h,FreeGroup.mk_toWord]
  have hlen : FreeGroup.norm z = L.length + R.length := by
    change z.toWord.length = _
    rw [← h,List.length_append]
  have hl : FreeGroup.norm (FreeGroup.mk L) ≤ L.length :=
    FreeGroup.norm_mk_le
  have hr : FreeGroup.norm (FreeGroup.mk R) ≤ R.length :=
    FreeGroup.norm_mk_le
  have hp := FreeGroup.norm_mul_le (FreeGroup.mk L) (FreeGroup.mk R)
  rw [hprod,hlen] at hp
  exact ⟨by omega,by omega⟩

/-- For every genuine single cut of the canonical outer word, both
new peripheral readings are nonidentity and the two inverse readings
multiply in reverse order to the original boundary. Their free-group
norms add exactly. Separation of the ribbon is not needed here. -/
theorem guba21_boundary_cut_reduced_factors
    (rows : I → RawWord) (w : F) (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∀ b, a ≠ b → P.rotation.SameCycle a b →
      let Q := P.vertexCut a b
      let u := (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹
      let v := (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹
      u ≠ 1 ∧ v ≠ 1 ∧ v * u = w ∧
        FreeGroup.norm u + FreeGroup.norm v = FreeGroup.norm w := by
  classical
  intro P a read b hne hsame Q u v
  let L := (Q.vertexBoundary a).map read
  let R := (Q.vertexBoundary b).map read
  have hcat : L ++ R = (w⁻¹).toWord := by
    change (Q.vertexBoundary a).map read ++
      (Q.vertexBoundary b).map read = _
    rw [← List.map_append]
    change (((P.vertexCut a b).vertexBoundary a ++
      (P.vertexCut a b).vertexBoundary b).map read) = _
    rw [← vertexCut_partition P a b hne hsame]
    exact (boundaryRibbon_read rows w s hs hw).trans
      (FreeGroup.toWord_inv w).symm
  obtain ⟨hl,hr⟩ := canonical_split_norm w⁻¹ L R hcat
  have hL : 0 < L.length := by
    change 0 < ((Q.vertexBoundary a).map read).length
    rw [List.length_map]
    exact List.length_pos_iff.mpr (cycleBoundary_ne_nil Q.rotation a)
  have hR : 0 < R.length := by
    change 0 < ((Q.vertexBoundary b).map read).length
    rw [List.length_map]
    exact List.length_pos_iff.mpr (cycleBoundary_ne_nil Q.rotation b)
  have hu : FreeGroup.norm u = L.length := by
    change FreeGroup.norm (FreeGroup.mk L)⁻¹ = L.length
    rw [FreeGroup.norm_inv_eq,hl]
  have hv : FreeGroup.norm v = R.length := by
    change FreeGroup.norm (FreeGroup.mk R)⁻¹ = R.length
    rw [FreeGroup.norm_inv_eq,hr]
  have hprod : FreeGroup.mk L * FreeGroup.mk R = w⁻¹ := by
    rw [FreeGroup.mul_mk,hcat,FreeGroup.mk_toWord]
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    rw [he,FreeGroup.norm_one] at hu
    omega
  · intro he
    rw [he,FreeGroup.norm_one] at hv
    omega
  · change (FreeGroup.mk R)⁻¹ * (FreeGroup.mk L)⁻¹ = w
    rw [← mul_inv_rev,hprod,inv_inv]
  · rw [hu,hv]
    have hlen := congrArg List.length hcat
    rw [List.length_append] at hlen
    change L.length + R.length = FreeGroup.norm w⁻¹ at hlen
    rw [FreeGroup.norm_inv_eq] at hlen
    exact hlen

/-- The separating-cut induction rule now needs only the actual
geometric separation, not independent hypotheses asserting that the
two peripheral words are nontrivial. It also records the exact
boundary factorization and norm conservation. -/
theorem guba21_separating_cut_canonical_induction
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s) (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∀ b, a ≠ b → P.rotation.SameCycle a b →
      let Q := P.vertexCut a b
      ¬ Q.SameComponent a b →
      let u := (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹
      let v := (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹
      u ≠ 1 ∧ v ≠ 1 ∧ v * u = w ∧
      FreeGroup.norm u + FreeGroup.norm v = FreeGroup.norm w ∧
      ∃ l r : Peiffer.Sequence F (RankHeight n),
        RankMinimalExpression pick X n u l ∧
        RankMinimalExpression pick X n v r ∧
        (∀ j, rankCount s j = rankCount l j + rankCount r j) ∧
        descendingCountLT n rankCount l s ∧
        descendingCountLT n rankCount r s := by
  intro rows P a read b hne hsame Q hsep u v
  obtain ⟨hu,hv,hprod,hnorm⟩ :=
    guba21_boundary_cut_reduced_factors rows w s hs hw b hne hsame
  refine ⟨hu,hv,hprod,hnorm,?_⟩
  exact guba21_actual_separating_cut_induction pick X n w s hm hw hs
    b hne hsame hsep hu hv

#print axioms canonical_split_norm
#print axioms guba21_boundary_cut_reduced_factors
#print axioms guba21_separating_cut_canonical_induction


/-- Exact local criterion for separation of a spherical ribbon by
a cut inside one vertex: the old predecessor corners belong to
the same face. The nontrivial direction follows from Euler's
inequality and the actual change in vertex and face counts. -/
theorem spherical_vertexCut_separates_iff {D : Type} [Fintype D]
    (P : RibbonMap D) (hE : P.EulerEquality) (a b : D)
    (hne : a ≠ b) (hsame : P.rotation.SameCycle a b) :
    ¬ (P.vertexCut a b).SameComponent a b ↔
      P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b) := by
  classical
  constructor
  · exact P.vertexCut_face_sameCycle_of_split a b
  · intro hpred hnew
    have hv := P.vertexCut_card_vertices_of_sameCycle a b hne hsame
    have he := Fintype.card_congr (P.vertexCutEdgeEquiv a b)
    have hc := Fintype.card_congr
      (P.vertexCutComponentsEquiv a b (P.component_of_vertexCycle hsame) hnew)
    have hf : Fintype.card (P.vertexCut a b).Face = Fintype.card P.Face + 1 := by
      let : Fintype (Cycles P.face) := inferInstanceAs (Fintype P.Face)
      let := Fintype.ofFinite (Cycles (cutAt P.face (P.rotation.symm a) (P.rotation.symm b)))
      have hcast := Fintype.card_congr (Equiv.cast (congrArg Cycles (P.vertexCut_face a b)))
      exact hcast.trans (card_cutAt_of_sameCycle P.face (P.rotation.symm a)
        (P.rotation.symm b) (P.rotation.symm.injective.ne hne) hpred)
    have hu := (P.vertexCut a b).euler_upper_bound
    change Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
    omega

/-- In the weighted metric of Guba, a canonical split still has
exact additivity: both factors are infixes of a reduced word. -/
theorem canonical_split_weight (z : F) (L R : RawWord)
    (h : L ++ R = z.toWord) :
    weightedLength (FreeGroup.mk L) = rawWeight L ∧
    weightedLength (FreeGroup.mk R) = rawWeight R := by
  have hr : FreeGroup.IsReduced (L ++ R) := by
    rw [h]
    exact FreeGroup.isReduced_toWord
  have hl' : FreeGroup.IsReduced L :=
    hr.infix ⟨[], R, by simp⟩
  have hr' : FreeGroup.IsReduced R :=
    hr.infix ⟨L, [], by simp⟩
  constructor
  · rw [weightedLength,FreeGroup.toWord_mk,hl'.reduce_eq]
  · rw [weightedLength,FreeGroup.toWord_mk,hr'.reduce_eq]

/-- Exact weighted perimeter conservation for the actual cut,
including the unequal weights of the two generators. -/
theorem guba21_boundary_cut_weight_additive
    (rows : I → RawWord) (w : F) (s : Peiffer.Sequence F I)
    (hs : Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) s = w)
    (hw : w ≠ 1) :
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    ∀ b, a ≠ b → P.rotation.SameCycle a b →
      let Q := P.vertexCut a b
      let u := (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹
      let v := (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹
      weightedLength u + weightedLength v = weightedLength w := by
  intro P a read b hne hsame Q u v
  let L := (Q.vertexBoundary a).map read
  let R := (Q.vertexBoundary b).map read
  have hcat : L ++ R = (w⁻¹).toWord := by
    change (Q.vertexBoundary a).map read ++
      (Q.vertexBoundary b).map read = _
    rw [← List.map_append]
    change (((P.vertexCut a b).vertexBoundary a ++
      (P.vertexCut a b).vertexBoundary b).map read) = _
    rw [← vertexCut_partition P a b hne hsame]
    exact (boundaryRibbon_read rows w s hs hw).trans
      (FreeGroup.toWord_inv w).symm
  obtain ⟨hl,hr⟩ := canonical_split_weight w⁻¹ L R hcat
  have winv (x : F) : weightedLength x⁻¹ = weightedLength x := by
    simp only [weightedLength,FreeGroup.toWord_inv,rawWeight_invRev]
  change weightedLength (FreeGroup.mk L)⁻¹ +
    weightedLength (FreeGroup.mk R)⁻¹ = weightedLength w
  rw [winv (FreeGroup.mk L),winv (FreeGroup.mk R),hl,hr,← rawWeight_append,hcat]
  exact winv w

/-- The all-cell perimeter conclusion of Lemma 23 is preserved by
a separating reassembly. The argument uses the original occurrence
indices, not just rank counts (which forget the height of a row).
This is the actual smaller-type induction step once the two
indexed fillings of the cut are supplied. -/
theorem guba23_reassembly_perimeter
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w u v : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s)
    (l r : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)))
    (hn : ((r ++ l).map Prod.fst).Nodup)
    (hlabel : ∀ x ∈ r ++ l, x.2.1.2 = s[x.1.val].1.2)
    (hl : RankMinimalExpression pick X n u (l.map Prod.snd))
    (hr : RankMinimalExpression pick X n v (r.map Prod.snd))
    (hprod : v * u = w)
    (hweight : weightedLength u + weightedLength v = weightedLength w)
    (hsmallL : descendingCountLT n rankCount (l.map Prod.snd) s)
    (hsmallR : descendingCountLT n rankCount (r.map Prod.snd) s)
    (ih : ∀ z t, RankMinimalExpression pick X n z t →
      descendingCountLT n rankCount t s →
      ∀ x ∈ t, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
        5 * weightedLength z) :
    ∀ x ∈ s, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
      5 * weightedLength w := by
  have he : Peiffer.evaluation (rankHeightRel pick X n) ((r ++ l).map Prod.snd) = w := by
    rw [List.map_append,peiffer_evaluation_append,hr.1,hl.1,hprod]
  have hall := rankMinimal_no_omitted_indices pick X n w s
    ((r ++ l).map Prod.snd) hm he ((r ++ l).map Prod.fst) hn
    (indexed_rankCount_eq s (r ++ l) hlabel)
  intro x hx
  obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
  let k : Fin s.length := ⟨i,hi⟩
  obtain ⟨t,ht,htk⟩ := List.mem_map.mp (hall k)
  have hrow := hlabel t ht
  have hxrow : t.2.1.2 = x.1.2 := by
    let rowAt : Fin s.length → RankHeight n := fun j => s[j.val].1.2
    calc
      _ = rowAt t.1 := hrow
      _ = rowAt k := congrArg rowAt htk
      _ = x.1.2 := congrArg (fun y : Peiffer.Occurrence F (RankHeight n) => y.1.2) hix
  rcases List.mem_append.mp ht with ht | ht
  · have h := ih v (r.map Prod.snd) hr hsmallR t.2
      (List.mem_map.mpr ⟨t,ht,rfl⟩)
    rw [hxrow] at h
    omega
  · have h := ih u (l.map Prod.snd) hl hsmallL t.2
      (List.mem_map.mpr ⟨t,ht,rfl⟩)
    rw [hxrow] at h
    omega

#print axioms spherical_vertexCut_separates_iff
#print axioms canonical_split_weight
#print axioms guba21_boundary_cut_weight_additive
#print axioms guba23_reassembly_perimeter


/-- Discharge the all-cell perimeter estimate at a separating
outer cut by smaller-type induction, using the actual indexed
fillings and the original weighted boundary. -/
theorem guba23_perimeter_at_separating_cut
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hm : RankMinimalExpression pick X n w s) (hw : w ≠ 1)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (ih : ∀ z t, RankMinimalExpression pick X n z t →
      descendingCountLT n rankCount t s →
      ∀ x ∈ t, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
        5 * weightedLength z) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    ∀ b, a ≠ b → P.rotation.SameCycle a b →
      ¬ (P.vertexCut a b).SameComponent a b →
      ∀ x ∈ s, 4 * rawWeight (rows x.1.2) < 5 * weightedLength w := by
  classical
  intro rows P a b hne hsame hsep
  let Q := P.vertexCut a b
  let tau := Q.rotation
  let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
  let u := (FreeGroup.mk ((Q.vertexBoundary a).map read))⁻¹
  let v := (FreeGroup.mk ((Q.vertexBoundary b).map read))⁻¹
  have hQ : P.withRotation tau = Q := by
    apply RibbonMap.ext <;> rfl
  have href : SplitRefinement P.rotation tau :=
    SplitRefinement.single P.rotation a b hne hsame
  have hpart : P.vertexBoundary a =
      (P.withRotation tau).vertexBoundary a ++
        (P.withRotation tau).vertexBoundary b := by
    rw [hQ]
    exact vertexCut_partition P a b hne hsame
  have hint : ∀ c ∈ [a,b], ∀ d, (P.withRotation tau).SameComponent c d →
      ¬ tau.SameCycle c d →
      discOccurrence (markedRows rows w) (boundaryIdentity s) d ≠
        boundaryOccurrence s ∧
        (P.withRotation tau).vertexBoundary d = P.vertexBoundary d := by
    intro c hc d hcd hnot
    rw [hQ] at hcd ⊢
    obtain ⟨hold,hread⟩ := separating_vertexCut_intact P a b hne hsame
      hsep c hc d hcd hnot
    exact ⟨fun he => hold ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr he),hread⟩
  have hsep' : ¬ (P.withRotation tau).SameComponent a b := by
    rw [hQ]
    exact hsep
  obtain ⟨l,r,hn,hla,hrb,_,_,hl,hr,hcount⟩ :=
    guba21_separating_boundary_cut_minimal pick X n w s hm hw hs tau
      b href hsep' hpart hint
  change RankMinimalExpression pick X n
    (FreeGroup.mk (((P.withRotation tau).vertexBoundary a).map read))⁻¹
      (l.map Prod.snd) at hl
  change RankMinimalExpression pick X n
    (FreeGroup.mk (((P.withRotation tau).vertexBoundary b).map read))⁻¹
      (r.map Prod.snd) at hr
  rw [hQ] at hl hr
  obtain ⟨hu,hv,hprod,_⟩ :=
    guba21_boundary_cut_reduced_factors rows w s hs hw b hne hsame
  have hweight :=
    guba21_boundary_cut_weight_additive rows w s hs hw b hne hsame
  have hln : l.map Prod.snd ≠ [] := by
    intro he
    apply hu
    have h := hl.1
    rw [he] at h
    exact h.symm
  have hrn : r.map Prod.snd ≠ [] := by
    intro he
    apply hv
    have h := hr.1
    rw [he] at h
    exact h.symm
  obtain ⟨hlt,hrt⟩ := guba21_separating_profiles_strict s
    (l.map Prod.snd) (r.map Prod.snd) hln hrn hcount
  have hn' : ((r ++ l).map Prod.fst).Nodup := by
    rw [List.map_append,List.nodup_append] at hn ⊢
    exact ⟨hn.2.1,hn.1,fun x hx y hy he => hn.2.2 y hy x hx he.symm⟩
  have hlabel (x : Fin s.length × Peiffer.Occurrence F (RankHeight n))
      (hx : x ∈ r ++ l) : x.2.1.2 = s[x.1.val].1.2 := by
    rcases List.mem_append.mp hx with hx | hx
    · exact (hrb x hx).1
    · exact (hla x hx).1
  exact guba23_reassembly_perimeter pick X n w u v s hm l r
    hn' hlabel hl hr hprod hweight hlt hrt ih

/-- The remaining perimeter problem can be restricted to diagrams
whose fixed outer base corner cannot be separated from any other
corner of that vertex by a single cut. This is a based condition,
not the stronger assertion of pairwise distinct incident faces.
The reduction makes no claim about that remaining geometry. -/
theorem guba23_perimeter_reduce_to_based_nonseparating
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ)
    (step : ∀ w (s : Peiffer.Sequence F (RankHeight n)),
      RankMinimalExpression pick X n w s → ∀ hw : w ≠ 1,
      ∀ hs : Peiffer.evaluation
        (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w,
      (∀ z t, RankMinimalExpression pick X n z t →
        descendingCountLT n rankCount t s →
        ∀ x ∈ t, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
          5 * weightedLength z) →
      (let P := boundaryRibbon (rankHeightRows pick X n) w s hs
       let a := boundaryDart (rankHeightRows pick X n) w s hw
       ∀ b, a ≠ b → P.rotation.SameCycle a b →
         ¬ P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b)) →
      ∀ x ∈ s, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
        5 * weightedLength w) :
    ∀ w (s : Peiffer.Sequence F (RankHeight n)),
      RankMinimalExpression pick X n w s →
      ∀ x ∈ s, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
        5 * weightedLength w := by
  classical
  let A := Peiffer.Sequence F (RankHeight n)
  let prop : A → Prop := fun s =>
    ∀ w, RankMinimalExpression pick X n w s →
      ∀ x ∈ s, 4 * rawWeight (rankHeightRows pick X n x.1.2) <
        5 * weightedLength w
  have all : ∀ s, prop s := descending_count_induction n rankCount prop (by
    intro s ih w hm x hx
    have smaller (z : F) (t : A) (ht : RankMinimalExpression pick X n z t)
        (hlt : descendingCountLT n rankCount t s) :
        ∀ y ∈ t, 4 * rawWeight (rankHeightRows pick X n y.1.2) <
          5 * weightedLength z := ih t hlt z ht
    by_cases hw : w = 1
    · obtain ⟨j,hj,hxj⟩ := List.mem_iff_getElem.mp hx
      have hp : 0 < rankCount s x.1.2.1.val := by
        unfold rankCount
        apply List.length_pos_iff_exists_mem.mpr
        exact ⟨x,List.mem_filter.mpr ⟨hx,by simp⟩⟩
      have hlt : descendingCountLT n rankCount ([] : A) s := by
        apply descending_count_lt_of_pointwise
        · intro k _
          simp [rankCount]
        · exact ⟨x.1.2.1.val,x.1.2.1.isLt,by simpa [rankCount] using hp⟩
      obtain ⟨k,hk,hstrict,habove⟩ := hlt
      have he : Peiffer.evaluation (rankHeightRel pick X n) ([] : A) = w := by
        rw [hw]
        rfl
      exact (Nat.not_lt_of_ge (hm.2 [] he k hk
        (fun q hq hqn => (habove q hq hqn).symm)) hstrict).elim
    · have hs : Peiffer.evaluation
          (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w := by
        simpa only [rankHeightRows_eval] using hm.1
      let P := boundaryRibbon (rankHeightRows pick X n) w s hs
      let a := boundaryDart (rankHeightRows pick X n) w s hw
      by_cases hface : ∃ b, a ≠ b ∧ P.rotation.SameCycle a b ∧
          P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b)
      · obtain ⟨b,hne,hsame,hf⟩ := hface
        have hsep := (spherical_vertexCut_separates_iff P
          (boundaryRibbon_euler _ w s hs) a b hne hsame).mpr hf
        exact guba23_perimeter_at_separating_cut pick X n w s hm hw hs
          smaller b hne hsame hsep x hx
      · apply step w s hm hw hs smaller _ x hx
        intro P' a' b hne hsame hf
        exact hface ⟨b,hne,hsame,hf⟩)
  intro w s hm
  exact all s w hm

/-- The exact 8.8(a) target follows from the remaining based
nonseparating geometric step of Lemma 23 for the constructed rows.
No global large-cell estimate is used as an axiom. -/
theorem answer_of_guba_based_nonseparating_step
    (pick : WeightedSelector)
    (step : ∀ n w (s : Peiffer.Sequence F (RankHeight n)),
      RankMinimalExpression pick (gubaConjugatorChoice pick) n w s →
      ∀ hw : w ≠ 1,
      ∀ hs : Peiffer.evaluation
        (fun i => FreeGroup.mk (rankHeightRows pick (gubaConjugatorChoice pick) n i)) s = w,
      (∀ z t, RankMinimalExpression pick (gubaConjugatorChoice pick) n z t →
        descendingCountLT n rankCount t s →
        ∀ x ∈ t, 4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n x.1.2) <
          5 * weightedLength z) →
      (let P := boundaryRibbon (rankHeightRows pick (gubaConjugatorChoice pick) n) w s hs
       let a := boundaryDart (rankHeightRows pick (gubaConjugatorChoice pick) n) w s hw
       ∀ b, a ≠ b → P.rotation.SameCycle a b →
         ¬ P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b)) →
      ∀ x ∈ s, 4 * rawWeight (rankHeightRows pick (gubaConjugatorChoice pick) n x.1.2) <
        5 * weightedLength w) : answer := by
  apply answer_of_guba_large_cell pick
  intro n w hmem hw
  obtain ⟨s,hm⟩ := exists_rankMinimalExpression pick (gubaConjugatorChoice pick) n w hmem
  have hne : s ≠ [] := by
    intro he
    apply hw
    have h := hm.1
    rw [he] at h
    exact h.symm
  obtain ⟨x,hx⟩ := List.length_pos_iff_exists_mem.mp (List.length_pos_iff.mpr hne)
  have hper := guba23_perimeter_reduce_to_based_nonseparating
    pick (gubaConjugatorChoice pick) n (step n) w s hm x hx
  obtain ⟨p,r,he⟩ := List.mem_iff_append.mp hx
  have hnon : rankHeightRows pick (gubaConjugatorChoice pick) n x.1.2 ≠ [] := by
    apply rankMinimal_designated_row_nonempty pick (gubaConjugatorChoice pick) n w p r x
    have hsplit : s = p ++ [x] ++ r := by simpa using he
    exact hsplit ▸ hm
  exact ⟨x.1.2,hnon,hper⟩

#print axioms guba23_perimeter_at_separating_cut
#print axioms guba23_perimeter_reduce_to_based_nonseparating
#print axioms answer_of_guba_based_nonseparating_step


/-- Raw weighted perimeter is independent of the based corner,
without assuming that the cyclic reading is freely reduced. -/
theorem ribbon_vertex_weight_sameCycle {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (a b : D)
    (hab : P.rotation.SameCycle a b) :
    rawWeight ((P.vertexBoundary b).map read) =
      rawWeight ((P.vertexBoundary a).map read) := by
  exact (ribbon_perimeter_sameCycle P read a b hab).symm


/-- In a shortest nontrivial kernel word every based cyclic reading
is itself canonical. This uses minimality in the weighted metric,
not a general assertion that every relator spelling is reduced. -/
theorem shortest_kernel_cyclic_read {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (a b : D) (hab : P.rotation.SameCycle a b)
    (w : F) (hw : w ≠ 1) (hm : w ∈ N)
    (hbase : (P.vertexBoundary a).map read = w.toWord)
    (hmin : ∀ z : F, z ∈ N → z ≠ 1 → weightedLength w ≤ weightedLength z) :
    (FreeGroup.mk ((P.vertexBoundary b).map read)).toWord =
      (P.vertexBoundary b).map read := by
  let z := FreeGroup.mk ((P.vertexBoundary b).map read)
  have ha : FreeGroup.mk ((P.vertexBoundary a).map read) = w := by
    rw [hbase,FreeGroup.mk_toWord]
  have hz : z ∈ N :=
    (ribbon_vertex_mem_sameCycle P read N a b hab).mp (by rw [ha]; exact hm)
  have hne : z ≠ 1 := by
    obtain ⟨u,hu,_⟩ := vertex_short_corner_connector P read a b hab
    rw [ha] at hu
    change w * FreeGroup.mk u = FreeGroup.mk u * z at hu
    intro he
    rw [he,mul_one] at hu
    exact hw (mul_right_cancel (hu.trans (one_mul _).symm))
  have hle := weightedLength_mk_le ((P.vertexBoundary b).map read)
  have hweight := ribbon_vertex_weight_sameCycle P read a b hab
  rw [hbase] at hweight
  change rawWeight ((P.vertexBoundary b).map read) = weightedLength w at hweight
  apply rawWord_eq_of_sublist_weight
  · rw [FreeGroup.toWord_mk]
    exact FreeGroup.Red.sublist FreeGroup.reduce.red
  · change weightedLength z = rawWeight ((P.vertexBoundary b).map read)
    have hlow := hmin z hz hne
    change weightedLength z ≤ _ at hle
    omega

/-- No two distinct corners of a shortest nontrivial kernel boundary
can cut off a separate component. This works at EVERY corner,
and needs no graded minimality or all-cell perimeter induction. -/
theorem shortest_kernel_no_separating_cut {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (N : Subgroup F) [N.Normal]
    (hE : P.EulerEquality)
    (hedge : ∀ e, read (P.edge e) = reverseLetter (read e))
    (a : D) (w : F) (hw : w ≠ 1) (hm : w ∈ N)
    (hbase : (P.vertexBoundary a).map read = w.toWord)
    (hmin : ∀ z : F, z ∈ N → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (hint : ∀ e, ¬ P.rotation.SameCycle a e →
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N) :
    ∀ c d, P.rotation.SameCycle a c → P.rotation.SameCycle a d →
      c ≠ d → ¬ P.face.SameCycle (P.rotation.symm c) (P.rotation.symm d) := by
  intro c d hac had hne hf
  have hcd := hac.symm.trans had
  have hsep := (spherical_vertexCut_separates_iff P hE c d hne hcd).mpr hf
  let Q := P.vertexCut c d
  let L := (Q.vertexBoundary c).map read
  let R := (Q.vertexBoundary d).map read
  let z := FreeGroup.mk ((P.vertexBoundary c).map read)
  have hcat : L ++ R = z.toWord := by
    rw [shortest_kernel_cyclic_read P read N a c hac w hw hm hbase hmin]
    change (Q.vertexBoundary c).map read ++ (Q.vertexBoundary d).map read = _
    rw [← List.map_append]
    change (((P.vertexCut c d).vertexBoundary c ++
      (P.vertexCut c d).vertexBoundary d).map read) = _
    rw [← vertexCut_partition P c d hne hcd]
  obtain ⟨hl,hr⟩ := canonical_split_weight z L R hcat
  have hL : L ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    change ((Q.vertexBoundary c).map read).length = 0 at hlen
    rw [List.length_map] at hlen
    exact cycleBoundary_ne_nil Q.rotation c (List.length_eq_zero_iff.mp hlen)
  have hR : R ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    change ((Q.vertexBoundary d).map read).length = 0 at hlen
    rw [List.length_map] at hlen
    exact cycleBoundary_ne_nil Q.rotation d (List.length_eq_zero_iff.mp hlen)
  have hposL : 0 < rawWeight L := by
    by_contra! h
    exact hL ((rawWeight_eq_zero_iff L).mp (by omega))
  have hposR : 0 < rawWeight R := by
    by_contra! h
    exact hR ((rawWeight_eq_zero_iff R).mp (by omega))
  have hmem : FreeGroup.mk L ∈ N := by
    apply vertexCut_separated_boundary_mem P read N c d
      (Q.vertexBoundary c) (Q.vertexBoundary d) hne hcd hE hedge
      (vertexCut_partition P c d hne hcd) rfl rfl hsep
    intro e _ he
    exact hint e (fun hae => he (hac.symm.trans hae))
  have hnon : FreeGroup.mk L ≠ 1 := by
    intro h
    have hz := (weightedLength_eq_zero_iff _).mpr h
    omega
  have hlow := hmin (FreeGroup.mk L) hmem hnon
  have hweight := ribbon_vertex_weight_sameCycle P read a c hac
  rw [hbase,vertexCut_partition P c d hne hcd,List.map_append,rawWeight_append] at hweight
  change rawWeight L + rawWeight R = weightedLength w at hweight
  omega

/-- At the first failing rank it suffices to exclude the shortest
nonidentity kernel word of weight at most that of the commutator.
The preceding stage is short-word injective, and every proper
shorter nonidentity word survives even at the failing stage. -/
theorem answer_of_first_shortest_kernel_step (pick : WeightedSelector)
    (X : ConjugatorChoice)
    (step : ∀ j w,
      (∀ z : F, z ∈ weightedHeightStage pick X j →
        weightedLength z ≤ 2 + 2 * 10^80 → z = 1) →
      w ∈ weightedHeightStage pick X (j+1) → w ≠ 1 →
      weightedLength w ≤ 2 + 2 * 10^80 →
      (∀ z : F, z ∈ weightedHeightStage pick X (j+1) →
        z ≠ 1 → weightedLength w ≤ weightedLength z) → False) :
    answer := by
  apply answer_of_heightStages_short pick X
  intro n
  induction n with
  | zero =>
    intro w hw _
    rw [weightedHeightStage_eq] at hw
    exact hw
  | succ j ih =>
    intro w hw hlen
    by_contra hn
    let p : ℕ → Prop := fun m => ∃ z : F,
      z ∈ weightedHeightStage pick X (j+1) ∧ z ≠ 1 ∧ weightedLength z = m
    have hex : ∃ m, p m := ⟨weightedLength w,w,hw,hn,rfl⟩
    classical
    obtain ⟨v,hv,hvn,hve⟩ := Nat.find_spec hex
    have hmin (z : F) (hz : z ∈ weightedHeightStage pick X (j+1))
        (hzn : z ≠ 1) : weightedLength v ≤ weightedLength z := by
      rw [hve]
      exact Nat.find_min' hex ⟨z,hz,hzn,rfl⟩
    exact step j v ih hv hvn ((hmin w hw hn).trans hlen) hmin

#print axioms ribbon_vertex_weight_sameCycle
#print axioms shortest_kernel_cyclic_read
#print axioms shortest_kernel_no_separating_cut
#print axioms answer_of_first_shortest_kernel_step


/-- Apply the shortest-kernel argument to the actual marked ribbon
of the recursive rank presentation, with no hypotheses about
the signs, counts, or distribution of its interior occurrences. -/
theorem rankRibbon_shortest_kernel_distinct_faces
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (hw : w ≠ 1) (hm : w ∈ weightedHeightStage pick X n)
    (hmin : ∀ z : F, z ∈ weightedHeightStage pick X n →
      z ≠ 1 → weightedLength w ≤ weightedLength z) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let a := boundaryDart rows w s hw
    ∀ c d, P.rotation.SameCycle a c → P.rotation.SameCycle a d →
      c ≠ d → ¬ P.face.SameCycle (P.rotation.symm c) (P.rotation.symm d) := by
  classical
  intro rows P a
  let N := weightedHeightStage pick X n
  let : N.Normal := by
    unfold N
    rw [← rankHeight_normalClosure]
    infer_instance
  let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
  have winv (z : F) : weightedLength z⁻¹ = weightedLength z := by
    simp only [weightedLength,FreeGroup.toWord_inv,rawWeight_invRev]
  have hbase : (P.vertexBoundary a).map read = (w⁻¹).toWord :=
    (boundaryRibbon_read rows w s hs hw).trans (FreeGroup.toWord_inv w).symm
  have hinterior (e : DiscDarts (markedRows rows w) (boundaryIdentity s))
      (he : ¬ P.rotation.SameCycle a e) :
      FreeGroup.mk ((P.vertexBoundary e).map read) ∈ N := by
    have hinteriorLabel (k : Fin (boundaryIdentity s).length)
        (hk : k ≠ boundaryOccurrence s) :
        ∃ i : RankHeight n, (boundaryIdentity s)[k].1.2 = some i := by
      obtain ⟨v,hv⟩ := k
      cases v with
      | zero => exact (hk (Fin.ext rfl)).elim
      | succ m =>
        have hm' : m < s.length := by simpa [boundaryIdentity] using hv
        refine ⟨s[m].1.2,?_⟩
        simp [boundaryIdentity,markOccurrence]
    have hk : discOccurrence (markedRows rows w) (boundaryIdentity s) e ≠
        boundaryOccurrence s :=
      fun h => he ((boundaryDart_sameVertex_iff rows w s hs hw e).mpr h)
    obtain ⟨i,hi⟩ := hinteriorLabel _ hk
    exact rankRibbon_lower_vertex_mem pick X n n w s hs e i hi i.1.isLt
  apply shortest_kernel_no_separating_cut P read N
    (boundaryRibbon_euler rows w s hs)
    (relatorRibbon_edge_read (chosenSection (Fin 2)) (markedRows rows w)
      (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs))
    a w⁻¹ (by simpa using hw) (N.inv_mem hm) hbase
  · intro z hz hne
    rw [winv]
    exact hmin z hz hne
  · exact hinterior

#print axioms rankRibbon_shortest_kernel_distinct_faces


/-- Every nonempty interval of a canonical word below the first
failure threshold survives in the preceding quotient. The full
interval is allowed; it need not be a proper factor. -/
theorem short_canonical_factor_survives
    (N : Subgroup F) (B : ℕ)
    (hshort : ∀ z : F, z ∈ N → weightedLength z ≤ B → z = 1)
    (z : F) (hbound : weightedLength z ≤ B)
    (u : RawWord) (hu : u ≠ []) (hfactor : u <:+: z.toWord) :
    FreeGroup.mk u ∉ N := by
  have hred : FreeGroup.IsReduced u := FreeGroup.isReduced_toWord.infix hfactor
  have hword : (FreeGroup.mk u).toWord = u := by
    rw [FreeGroup.toWord_mk,hred.reduce_eq]
  have hweight : weightedLength (FreeGroup.mk u) = rawWeight u := by
    rw [weightedLength,hword]
  have hle : rawWeight u ≤ weightedLength z := by
    obtain ⟨p,r,h⟩ := hfactor
    have he : z.toWord = p ++ u ++ r := by
      simpa only [List.append_assoc] using h.symm
    unfold weightedLength
    rw [he,rawWeight_append,rawWeight_append]
    omega
  intro hm
  have he := hshort (FreeGroup.mk u) hm (by omega)
  have hn : (FreeGroup.mk u).toWord = [] := FreeGroup.toWord_eq_nil_iff.mpr he
  exact hu (hword.symm.trans hn)

/-- Every nonempty interval at any corner of a shortest failing
kernel boundary survives in the previous stage. This uses the
stronger all-corners cyclic reduction, not just the fixed base. -/
theorem shortest_kernel_outer_factor_survives {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter)
    (N M : Subgroup F) [M.Normal] (B : ℕ)
    (hshort : ∀ z : F, z ∈ N → weightedLength z ≤ B → z = 1)
    (a c : D) (hac : P.rotation.SameCycle a c)
    (w : F) (hw : w ≠ 1) (hm : w ∈ M)
    (hbase : (P.vertexBoundary a).map read = w.toWord)
    (hmin : ∀ z : F, z ∈ M → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (hbound : weightedLength w ≤ B)
    (u : RawWord) (hu : u ≠ [])
    (hfactor : u <:+: (P.vertexBoundary c).map read) :
    FreeGroup.mk u ∉ N := by
  let z := FreeGroup.mk ((P.vertexBoundary c).map read)
  have hz : z.toWord = (P.vertexBoundary c).map read :=
    shortest_kernel_cyclic_read P read M a c hac w hw hm hbase hmin
  have hweight : weightedLength z = weightedLength w := by
    unfold weightedLength
    rw [hz,← hbase]
    exact (ribbon_perimeter_sameCycle P read a c hac).symm
  apply short_canonical_factor_survives N B hshort z (by omega) u hu
  rw [hz]
  exact hfactor

/-- A genuine contiguous outer block cannot be the sole peripheral
block of a lower-stage coefficient component of the shortest failure.
In contrast to a mere non-singleton dart count, the additional
outlet is outside the entire block. -/
theorem shortest_kernel_outer_block_has_other_outlet {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter)
    (N M : Subgroup F) [N.Normal] [M.Normal] (B : ℕ)
    (hshort : ∀ z : F, z ∈ N → weightedLength z ≤ B → z = 1)
    (keep : D → Prop) (hstep : ∀ d, keep (P.rotation d) ↔ keep d)
    (tau : Equiv.Perm D)
    (hE : P.EulerEquality) (href : SplitRefinement P.rotation tau)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hprotected : ∀ d, keep d →
      (P.withRotation tau).vertexBoundary d = P.vertexBoundary d)
    (hint : ∀ d, keep d → FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N)
    (hcomp : ∀ d e, (P.withRotation tau).SameComponent d e ↔
      (P.coefficientRegions keep hstep).SameComponent d e)
    (a c : D) (hac : P.rotation.SameCycle a c)
    (w : F) (hw : w ≠ 1) (hm : w ∈ M)
    (hbase : (P.vertexBoundary a).map read = w.toWord)
    (hmin : ∀ z : F, z ∈ M → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (hbound : weightedLength w ≤ B)
    (d : D) (u : List D)
    (hread : (P.withRotation tau).vertexBoundary d = d :: u)
    (hfactor : (d :: u).map read <:+: (P.vertexBoundary c).map read) :
    ∃ e, (P.coefficientRegions keep hstep).SameComponent d e ∧
      ¬ keep e ∧ e ∉ d :: u := by
  classical
  by_contra hn
  apply shortest_kernel_outer_factor_survives P read N M B hshort
    a c hac w hw hm hbase hmin hbound ((d :: u).map read) (by simp) hfactor
  apply coefficient_one_block_mem P read N keep hstep tau hE href
    hedge hprotected hint hcomp d u hread
  intro e he hk
  by_contra hmem
  exact hn ⟨e,he,hk,hmem⟩

#print axioms short_canonical_factor_survives
#print axioms shortest_kernel_outer_factor_survives
#print axioms shortest_kernel_outer_block_has_other_outlet


/-- At the top rank, equality modulo the entire preceding stage
is enough to test minimality. No replacement geometry is needed
once an algebraic quotient identity has been obtained. -/
theorem rankMinimal_top_count_of_modular_filling
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ)
    (w : F) (s t : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s)
    (he : (Peiffer.evaluation (rankHeightRel pick X (j+1)) t)⁻¹ * w ∈
      weightedHeightStage pick X j) :
    rankCount s j ≤ rankCount t j := by
  by_contra! hlt
  have hm' : RankMinimalExpression pick X (j+1) w ([] ++ s ++ []) := by
    simpa using hm
  apply rankMinimal_block_no_reduction_mod_lower pick X (j+1) w [] s [] t
    hm' j (Nat.lt_succ_self j)
  · rw [hm.1]
    exact he
  · intro k hk hkn
    omega
  · exact hlt

/-- A finite list of top-rank conjugating bases and heights is a
genuine filling with exactly that many top-rank occurrences. -/
def topRankFilling (j : ℕ) (l : List (F × ℤ)) :
    Peiffer.Sequence F (RankHeight (j+1)) :=
  l.map (fun x => ((x.1,(⟨j,Nat.lt_succ_self j⟩,x.2)),true))

theorem topRankFilling_count (j : ℕ) (l : List (F × ℤ)) :
    rankCount (topRankFilling j l) j = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change rankCount ([((x.1,(⟨j,Nat.lt_succ_self j⟩,x.2)),true)] ++
      topRankFilling j xs) j = xs.length + 1
    rw [rankCount_append,rankCount_singleton,ih]
    simp [Nat.add_comm]

theorem topRankFilling_evaluation (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ) (l : List (F × ℤ)) :
    Peiffer.evaluation (rankHeightRel pick X (j+1)) (topRankFilling j l) =
      (l.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change (x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹) *
      Peiffer.evaluation (rankHeightRel pick X (j+1)) (topRankFilling j xs) = _
    rw [ih]
    rfl

/-- Any proposed expression in conjugates of the top-rank height
relators in the preceding quotient has at least the original top
count. The bases may be arbitrary representatives in the free group. -/
theorem rankMinimal_top_quotient_lower_bound
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s)
    (l : List (F × ℤ))
    (he : ((l.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod)⁻¹ *
      w ∈ weightedHeightStage pick X j) :
    rankCount s j ≤ l.length := by
  rw [← topRankFilling_count j l]
  apply rankMinimal_top_count_of_modular_filling pick X j w s
    (topRankFilling j l) hm
  rw [topRankFilling_evaluation]
  exact he

/-- Remove all earlier-rank occurrences from a positive expression
in the preceding quotient, without altering the order or heights
of the surviving top-rank occurrences. -/
theorem topRank_project_filling (pick : WeightedSelector)
    (X : ConjugatorChoice) (j : ℕ)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hpos : ∀ x ∈ s, x.2 = true) :
    let N := weightedStages pick X j
    letI : N.Normal := weightedStages_normal pick X j
    let q := QuotientGroup.mk' N
    ∃ l : List (F × ℤ), l.length = rankCount s j ∧
      q (Peiffer.evaluation (rankHeightRel pick X (j+1)) s) =
        q ((l.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod) := by
  classical
  let N := weightedStages pick X j
  let : N.Normal := weightedStages_normal pick X j
  let q := QuotientGroup.mk' N
  change ∃ l : List (F × ℤ), l.length = rankCount s j ∧
    q (Peiffer.evaluation (rankHeightRel pick X (j+1)) s) =
      q ((l.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod)
  induction s with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨l,hl,he⟩ := ih (fun y hy => hpos y (List.mem_cons_of_mem _ hy))
    have hx := hpos x (List.mem_cons_self)
    rcases x with ⟨⟨u,⟨i,k⟩⟩,sg⟩
    change sg = true at hx
    subst sg
    have hcount : rankCount (((u,(i,k)),true) :: xs) j =
        (if i.val = j then 1 else 0) + rankCount xs j := by
      change rankCount ([((u,(i,k)),true)] ++ xs) j = _
      rw [rankCount_append,rankCount_singleton]
    have hterm : Peiffer.term (rankHeightRel pick X (j+1)) ((u,(i,k)),true) =
        u * weightedRankHeightRelator pick X i.val k * u⁻¹ := rfl
    have hsplit : Peiffer.evaluation (rankHeightRel pick X (j+1)) (((u,(i,k)),true)::xs) =
        (u * weightedRankHeightRelator pick X i.val k * u⁻¹) *
          Peiffer.evaluation (rankHeightRel pick X (j+1)) xs := by
      change Peiffer.term (rankHeightRel pick X (j+1)) ((u,(i,k)),true) * _ = _
      rw [hterm]
      rfl
    by_cases hi : i.val = j
    · refine ⟨(u,k)::l,?_,?_⟩
      · rw [hcount,ite_eq_left hi,List.length_cons,hl]
        omega
      · rw [hsplit,hi,map_mul,he]
        simp only [List.map_cons,List.prod_cons,map_mul]
    · refine ⟨l,?_,?_⟩
      · rw [hcount,ite_eq_right hi,zero_add]
        exact hl
      · have hij : i.val < j := by omega
        have hm : weightedRankHeightRelator pick X i.val k ∈ N := by
          change _ ∈ weightedStages pick X j
          rw [← weightedHeightStage_eq]
          exact Subgroup.subset_normalClosure ⟨i.val,hij,k,rfl⟩
        have hq : q (u * weightedRankHeightRelator pick X i.val k * u⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr
            ((inferInstance : N.Normal).conj_mem _ hm _)
        rw [hsplit,map_mul,hq,one_mul,he]

/-- The first-stage obstruction is equivalent to a shortest
nonempty product in the quotient by the preceding stages.
This records both existence of the projected expression and its
global minimality against every proposed replacement. -/
theorem rankMinimal_top_quotient_exact
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s)
    (hpos : ∀ x ∈ s, x.2 = true)
    (hnew : w ∉ weightedHeightStage pick X j) :
    let N := weightedStages pick X j
    letI : N.Normal := weightedStages_normal pick X j
    let q := QuotientGroup.mk' N
    ∃ l : List (F × ℤ), l ≠ [] ∧ l.length = rankCount s j ∧
      q w = q ((l.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod) ∧
      ∀ t : List (F × ℤ),
        q w = q ((t.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod) →
        l.length ≤ t.length := by
  let N := weightedStages pick X j
  let : N.Normal := weightedStages_normal pick X j
  let q := QuotientGroup.mk' N
  obtain ⟨l,hl,he⟩ := topRank_project_filling pick X j s hpos
  change q (Peiffer.evaluation (rankHeightRel pick X (j+1)) s) = _ at he
  rw [hm.1] at he
  refine ⟨l,?_,hl,he,?_⟩
  · intro hn
    apply hnew
    rw [weightedHeightStage_eq]
    change w ∈ N
    have hq : q w = 1 := by
      rw [hn] at he
      simpa only [List.map_nil,List.prod_nil,map_one] using he
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro t ht
    rw [hl]
    apply rankMinimal_top_quotient_lower_bound pick X j w s hm t
    rw [weightedHeightStage_eq]
    apply (QuotientGroup.eq_one_iff _).mp
    change q (((t.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod)⁻¹ * w) = 1
    rw [map_mul,map_inv,ht,inv_mul_cancel]

#print axioms rankMinimal_top_count_of_modular_filling
#print axioms topRankFilling_count
#print axioms topRankFilling_evaluation
#print axioms rankMinimal_top_quotient_lower_bound
#print axioms topRank_project_filling
#print axioms rankMinimal_top_quotient_exact


/-- The quotient product of the conjugated height relators.
Keep bases in the free group so all proposed replacements lift
without making any choice of quotient representatives. -/
def topHeightProduct {K : Type} [Group K] (q : F →* K)
    (R : ℤ → F) (l : List (F × ℤ)) : K :=
  (l.map (fun x => q x.1 * q (R x.2) * (q x.1)⁻¹)).prod

theorem topHeightProduct_append {K : Type} [Group K] (q : F →* K)
    (R : ℤ → F) (l r : List (F × ℤ)) :
    topHeightProduct q R (l ++ r) =
      topHeightProduct q R l * topHeightProduct q R r := by
  simp only [topHeightProduct,List.map_append,List.prod_append]

theorem topHeightProduct_singleton {K : Type} [Group K] (q : F →* K)
    (R : ℤ → F) (u : F) (k : ℤ) :
    topHeightProduct q R [(u,k)] = q u * q (R k) * (q u)⁻¹ := by
  simp [topHeightProduct]

theorem topHeightProduct_map {K : Type} [Group K] (q : F →* K)
    (R : ℤ → F) (l : List (F × ℤ)) :
    q ((l.map (fun x => x.1 * R x.2 * x.1⁻¹)).prod) =
      topHeightProduct q R l := by
  induction l with
  | nil => simp [topHeightProduct]
  | cons x xs ih =>
    simp only [List.map_cons,List.prod_cons,map_mul,map_inv,ih,topHeightProduct]

/-- A transported alignment of the bases of two equal-rank cells
suffices for an exact merger in any quotient. The intervening
product is kept, including its order; it need not vanish. -/
theorem topHeightProduct_merge {K : Type} [Group K] (q : F →* K)
    (R : ℤ → F)
    (hadd : ∀ k l, R (k+l) = R k * a^k * R l * (a^k)⁻¹)
    (u v : F) (k l : ℤ) (m : List (F × ℤ))
    (halign : topHeightProduct q R m * q v = q u * q (a^k)) :
    topHeightProduct q R ([(u,k)] ++ m ++ [(v,l)]) =
      topHeightProduct q R ([(u,k+l)] ++ m) := by
  have hv : q v = (topHeightProduct q R m)⁻¹ * (q u * q (a^k)) := by
    calc
      _ = (topHeightProduct q R m)⁻¹ * (topHeightProduct q R m * q v) := by group
      _ = _ := by rw [halign]
  simp only [topHeightProduct_append,topHeightProduct_singleton,hadd,map_mul,map_inv]
  rw [hv]
  group

/-- In the exact top-rank quotient minimizer, no such transported
alignment can occur anywhere in the list. This is a consequence
of global minimality, not an additional geometric hypothesis. -/
theorem topRank_minimal_no_transported_merge
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ) (w : F)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s)
    (p m r : List (F × ℤ)) (u v : F) (k l : ℤ)
    (hcount : (p ++ [(u,k)] ++ m ++ [(v,l)] ++ r).length = rankCount s j) :
    let N := weightedStages pick X j
    letI : N.Normal := weightedStages_normal pick X j
    let q := QuotientGroup.mk' N
    let R := weightedRankHeightRelator pick X j
    q w = topHeightProduct q R (p ++ [(u,k)] ++ m ++ [(v,l)] ++ r) →
    topHeightProduct q R m * q v ≠ q u * q (a^k) := by
  intro N q R he halign
  let : N.Normal := weightedStages_normal pick X j
  let t := p ++ [(u,k+l)] ++ m ++ r
  have hmerge := topHeightProduct_merge q R
    (weightedRankHeightRelator_add pick X j) u v k l m halign
  have hnew : q w = topHeightProduct q R t := by
    calc
      _ = topHeightProduct q R (p ++ ([(u,k)] ++ m ++ [(v,l)]) ++ r) := by
        simpa only [List.append_assoc] using he
      _ = topHeightProduct q R (p ++ ([(u,k+l)] ++ m) ++ r) := by
        calc
          _ = (topHeightProduct q R p *
            topHeightProduct q R ([(u,k)] ++ m ++ [(v,l)])) * topHeightProduct q R r := by
              rw [topHeightProduct_append q R (p ++ ([(u,k)] ++ m ++ [(v,l)])) r,
                topHeightProduct_append q R p ([(u,k)] ++ m ++ [(v,l)])]
          _ = (topHeightProduct q R p *
            topHeightProduct q R ([(u,k+l)] ++ m)) * topHeightProduct q R r := by rw [hmerge]
          _ = _ := by
            rw [topHeightProduct_append q R (p ++ ([(u,k+l)] ++ m)) r,
              topHeightProduct_append q R p ([(u,k+l)] ++ m)]
      _ = _ := by simp only [t,List.append_assoc]
  have hmod : ((t.map (fun x => x.1 * weightedRankHeightRelator pick X j x.2 * x.1⁻¹)).prod)⁻¹ *
      w ∈ weightedHeightStage pick X j := by
    rw [weightedHeightStage_eq]
    apply (QuotientGroup.eq_one_iff _).mp
    change q (((t.map (fun x => x.1 * R x.2 * x.1⁻¹)).prod)⁻¹ * w) = 1
    rw [map_mul,map_inv,topHeightProduct_map,hnew,inv_mul_cancel]
  have hle := rankMinimal_top_quotient_lower_bound pick X j w s hm t hmod
  simp only [List.length_append,List.length_singleton] at hcount
  simp only [t,List.length_append,List.length_singleton] at hle
  omega

/-- Short equality in an earlier quotient lifts to exact free-group
equality when the sum of the two representative weights is within
the injectivity threshold. This isolates the precise metric budget
needed to turn a short coefficient connector into literal alignment. -/
theorem short_quotient_equality_lifts (N : Subgroup F) [N.Normal] (B : ℕ)
    (hshort : ∀ z : F, z ∈ N → weightedLength z ≤ B → z = 1)
    (x y : F) (hweight : weightedLength x + weightedLength y ≤ B)
    (he : QuotientGroup.mk' N x = QuotientGroup.mk' N y) : x = y := by
  have hm : x⁻¹ * y ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (x⁻¹ * y) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hinv : weightedLength x⁻¹ = weightedLength x := by
    simp only [weightedLength,FreeGroup.toWord_inv,rawWeight_invRev]
  have hle := weightedLength_mul_le x⁻¹ y
  rw [hinv] at hle
  have hz := hshort (x⁻¹*y) hm (hle.trans hweight)
  calc
    x = x * 1 := (mul_one _).symm
    _ = x * (x⁻¹*y) := by rw [hz]
    _ = y := by group

#print axioms topHeightProduct_append
#print axioms topHeightProduct_singleton
#print axioms topHeightProduct_map
#print axioms topHeightProduct_merge
#print axioms topRank_minimal_no_transported_merge
#print axioms short_quotient_equality_lifts


/-- The shortest nontrivial word killed at the new stage, provided
it survives the preceding stage, has no shorter representative
in the preceding quotient. This is stronger than free reduction. -/
theorem shortest_new_kernel_quotient_geodesic
    (N M : Subgroup F) [N.Normal] (hNM : N ≤ M)
    (w : F) (hm : w ∈ M) (hnew : w ∉ N)
    (hmin : ∀ z : F, z ∈ M → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (z : F) (he : QuotientGroup.mk' N w = QuotientGroup.mk' N z) :
    weightedLength w ≤ weightedLength z := by
  let q := QuotientGroup.mk' N
  have hdiff : w⁻¹ * z ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (w⁻¹ * z) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hz : z ∈ M := by
    have h := M.mul_mem hm (hNM hdiff)
    have hval : w * (w⁻¹*z) = z := by group
    rwa [hval] at h
  have hne : z ≠ 1 := by
    intro h
    apply hnew
    have hq : q w = 1 := by simpa only [h,map_one] using he
    exact (QuotientGroup.eq_one_iff _).mp hq
  exact hmin z hz hne

/-- Every literal interval in the shortest new kernel word is
geodesic in the previous quotient. In particular a contiguity
quadrilateral through earlier ranks cannot replace that interval
by a strictly shorter word. -/
theorem shortest_new_kernel_factor_geodesic
    (N M : Subgroup F) [N.Normal] (hNM : N ≤ M)
    (w : F) (hm : w ∈ M) (hnew : w ∉ N)
    (hmin : ∀ z : F, z ∈ M → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (p u r v : RawWord) (hword : w.toWord = p ++ u ++ r)
    (he : QuotientGroup.mk' N (FreeGroup.mk u) =
      QuotientGroup.mk' N (FreeGroup.mk v)) :
    rawWeight u ≤ rawWeight v := by
  have hreplace : QuotientGroup.mk' N w =
      QuotientGroup.mk' N (FreeGroup.mk (p ++ v ++ r)) := by
    calc
      _ = QuotientGroup.mk' N (FreeGroup.mk (p ++ u ++ r)) := by
        rw [← hword,FreeGroup.mk_toWord]
      _ = _ := by simp only [← FreeGroup.mul_mk,map_mul,he]
  have hlow := shortest_new_kernel_quotient_geodesic N M hNM w hm hnew hmin
    (FreeGroup.mk (p ++ v ++ r)) hreplace
  have hu := weightedLength_mk_le (p ++ v ++ r)
  have hweight : weightedLength w = rawWeight p + rawWeight u + rawWeight r := by
    unfold weightedLength
    rw [hword,rawWeight_append,rawWeight_append]
  rw [rawWeight_append,rawWeight_append] at hu
  omega

/-- The first failure is an isometrically embedded weighted cycle:
a connector between the endpoints of two complementary arcs
cannot have weight smaller than both arcs. This does not need a
planar diagram or any small-cancellation estimate. -/
theorem shortest_kernel_complementary_arc_bound
    (M : Subgroup F) [M.Normal]
    (w : F) (hw : w ≠ 1) (hm : w ∈ M)
    (hmin : ∀ z : F, z ∈ M → z ≠ 1 → weightedLength w ≤ weightedLength z)
    (u v : RawWord) (hword : u ++ v = w.toWord)
    (g : F) (he : QuotientGroup.mk' M (FreeGroup.mk u) = QuotientGroup.mk' M g) :
    min (rawWeight u) (rawWeight v) ≤ weightedLength g := by
  let q := QuotientGroup.mk' M
  let U := FreeGroup.mk u
  let V := FreeGroup.mk v
  have hprod : U * V = w := by
    change FreeGroup.mk u * FreeGroup.mk v = w
    rw [FreeGroup.mul_mk,hword,FreeGroup.mk_toWord]
  have hq : q (U * V) = 1 := by
    rw [hprod]
    exact (QuotientGroup.eq_one_iff _).mpr hm
  have h1 : U * g⁻¹ ∈ M := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (U * g⁻¹) = 1
    change q U = q g at he
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have h2 : g * V ∈ M := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * V) = 1
    rw [map_mul] at hq ⊢
    change q U = q g at he
    rwa [he] at hq
  have hi : weightedLength g⁻¹ = weightedLength g := by
    simp only [weightedLength,FreeGroup.toWord_inv,rawWeight_invRev]
  have hU := weightedLength_mk_le u
  have hV := weightedLength_mk_le v
  change weightedLength U ≤ rawWeight u at hU
  change weightedLength V ≤ rawWeight v at hV
  have hL := weightedLength_mul_le U g⁻¹
  have hR := weightedLength_mul_le g V
  rw [hi] at hL
  have hW : weightedLength w = rawWeight u + rawWeight v := by
    unfold weightedLength
    rw [← hword,rawWeight_append]
  by_contra! h
  have hgu : weightedLength g < rawWeight u := lt_of_lt_of_le h (min_le_left _ _)
  have hgv : weightedLength g < rawWeight v := lt_of_lt_of_le h (min_le_right _ _)
  have e1 : U * g⁻¹ = 1 := by
    by_contra hn
    have := hmin _ h1 hn
    omega
  have e2 : g * V = 1 := by
    by_contra hn
    have := hmin _ h2 hn
    omega
  apply hw
  calc
    w = (U * g⁻¹) * (g * V) := by rw [← hprod]; group
    _ = 1 := by rw [e1,e2,mul_one]

#print axioms shortest_new_kernel_quotient_geodesic
#print axioms shortest_new_kernel_factor_geodesic
#print axioms shortest_kernel_complementary_arc_bound


/-- A word of weight at most that of the heavy generator is either
a pure power of the light generator or one signed heavy letter. -/
theorem rawWord_at_most_heavy_weight (w : RawWord)
    (hw : rawWeight w ≤ 10^80) :
    (∃ k : ℤ, FreeGroup.mk w = a^k) ∨
      FreeGroup.mk w = b ∨ FreeGroup.mk w = b⁻¹ := by
  cases w with
  | nil => exact Or.inl ⟨0,by rw [zpow_zero,FreeGroup.one_eq_mk]⟩
  | cons x xs =>
    rcases x with ⟨i,sg⟩
    change letterWeight (i,sg) + rawWeight xs ≤ 10^80 at hw
    fin_cases i
    · have hlight : letterWeight ((0 : Fin 2),sg) = 1 := by simp [letterWeight]
      change letterWeight ((0 : Fin 2),sg) + rawWeight xs ≤ 10^80 at hw
      rw [hlight] at hw
      obtain ⟨k,hk⟩ := mk_eq_a_zpow_of_light xs (by omega)
      have hmul : FreeGroup.mk (((0 : Fin 2),sg)::xs) =
          FreeGroup.mk [(0,sg)] * FreeGroup.mk xs :=
        (FreeGroup.mul_mk (L₁ := [(0,sg)]) (L₂ := xs)).symm
      left
      change ∃ k : ℤ, FreeGroup.mk (((0 : Fin 2),sg)::xs) = a^k
      cases sg
      · refine ⟨-1+k,?_⟩
        rw [hmul,FreeGroup.mk_eq_inv_of,hk,zpow_add]
        simp [a]
      · refine ⟨1+k,?_⟩
        rw [hmul,FreeGroup.mk_eq_of,hk,zpow_add]
        simp [a]
    · have hheavy : letterWeight ((1 : Fin 2),sg) = 10^80 := by
        simp [letterWeight]
      change letterWeight ((1 : Fin 2),sg) + rawWeight xs ≤ 10^80 at hw
      rw [hheavy] at hw
      have hnil : xs = [] := (rawWeight_eq_zero_iff xs).mp (by omega)
      subst xs
      right
      change FreeGroup.mk [((1 : Fin 2),sg)] = b ∨ FreeGroup.mk [((1 : Fin 2),sg)] = b⁻¹
      cases sg
      · exact Or.inr (by rw [FreeGroup.mk_eq_inv_of]; rfl)
      · exact Or.inl (by rw [FreeGroup.mk_eq_of]; rfl)

/-- Before adding any relations, the heavy generator is not
conjugate to a power of the light generator. Detect it by the
homomorphism recording its exponent sum. -/
theorem heavy_not_good_bot : ¬ Good (⊥ : Subgroup F) b := by
  intro h
  obtain ⟨x,k,hx⟩ := h
  change x*b*x⁻¹*(a^k)⁻¹ = 1 at hx
  let f : Fin 2 → Multiplicative ℤ := fun i =>
    if i = 0 then 1 else Multiplicative.ofAdd 1
  let q : F →* Multiplicative ℤ := FreeGroup.lift f
  have ha : q a = 1 := by simp [q,f,a,FreeGroup.lift_apply_of]
  have hb : q b = Multiplicative.ofAdd 1 := by
    simp [q,f,b,FreeGroup.lift_apply_of]
  have he := congrArg q hx
  simp only [map_mul,map_inv,map_zpow,ha,one_zpow,inv_one,mul_one,map_one] at he
  have hzero : q b = 1 := by
    calc
      _ = (q x)⁻¹ * (q x * q b * (q x)⁻¹) * q x := by group
      _ = _ := by rw [he]; group
  rw [hb] at hzero
  exact (by decide : (Multiplicative.ofAdd (1 : ℤ)) ≠ 1) hzero

/-- Any weight-minimal bad period at the initial rank is exactly
one of the two signed heavy generators. -/
theorem initial_minBad_heavy (c : F) (hc : MinBad (⊥ : Subgroup F) c) :
    c = b ∨ c = b⁻¹ := by
  have hbw : weightedLength b = 10^80 := by
    simpa using weightedLength_b_zpow 1
  have hle := hc.2 b heavy_not_good_bot
  rw [hbw] at hle
  have h := rawWord_at_most_heavy_weight c.toWord hle
  rw [FreeGroup.mk_toWord] at h
  rcases h with ⟨k,hk⟩ | h
  · exfalso
    apply hc.1
    rw [hk]
    exact good_a_zpow ⊥ k
  · exact h

/-- When the two generators commute in an arbitrary target group,
the heavy generator commutes with the image of every free word. -/
theorem freeGroup_heavy_commutes_all {K : Type} [Group K] (q : F →* K)
    (hab : Commute (q a) (q b)) (x : F) :
    Commute (q x) (q b) := by
  have hgen (i : Fin 2) : Commute (q (FreeGroup.of i)) (q b) := by
    fin_cases i
    · exact hab
    · exact Commute.refl _
  have hraw (w : RawWord) : Commute (q (FreeGroup.mk w)) (q b) := by
    induction w with
    | nil =>
      rw [← FreeGroup.one_eq_mk,map_one]
      exact Commute.one_left _
    | cons y ys ih =>
      rcases y with ⟨i,sg⟩
      have he : FreeGroup.mk ((i,sg)::ys) =
          FreeGroup.mk [(i,sg)] * FreeGroup.mk ys :=
        (FreeGroup.mul_mk (L₁ := [(i,sg)]) (L₂ := ys)).symm
      rw [he,map_mul]
      cases sg
      · rw [FreeGroup.mk_eq_inv_of,map_inv]
        exact (hgen i).inv_left.mul_left ih
      · rw [FreeGroup.mk_eq_of]
        exact (hgen i).mul_left ih
  simpa only [FreeGroup.mk_toWord] using hraw x.toWord

/-- At rank one, one signed heavy generator is made conjugate to a.
If the commutator later vanishes, the conjugator disappears from
this equality: one of the two short words b*a or b*a^-1 is killed. -/
theorem weightedStages_comm_failure_shorter
    (pick : WeightedSelector) (X : ConjugatorChoice) (n : ℕ)
    (hm : commWord ∈ weightedStages pick X n) :
    b*a ∈ weightedStages pick X n ∨ b*a⁻¹ ∈ weightedStages pick X n := by
  have hn : 1 ≤ n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    subst n
    exact commWord_ne_one hm
  have hbad : ¬ Good (weightedStages pick X 0) b := heavy_not_good_bot
  -- Use the actual first defining relation with exponent one.
  let N0 := weightedStages pick X 0
  have h0 : ∃ w : F, ¬ Good N0 w := ⟨b,hbad⟩
  let C := (pick N0 h0).val
  have hC : C = b ∨ C = b⁻¹ := initial_minBad_heavy C (pick N0 h0).property
  let u := X 0 N0 C
  have hr : u*C*u⁻¹*a⁻¹ ∈ weightedStages pick X 1 := by
    change u*C*u⁻¹*a⁻¹ ∈ adjoin N0 (weightedRelator pick X 0 N0)
    rw [weightedRelator_eq pick X 0 N0 h0]
    simpa only [heightRelator_one] using (relator_mem_adjoin N0 (heightRelator u C 1))
  let N := weightedStages pick X n
  let : N.Normal := weightedStages_normal pick X n
  let q := QuotientGroup.mk' N
  have hrn : u*C*u⁻¹*a⁻¹ ∈ N := (weightedStages_mono pick X hn) hr
  have he : q (u*C*u⁻¹*a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hrn
  simp only [map_mul,map_inv] at he
  have hcomm : q commWord = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  change q (a*b*a⁻¹*b⁻¹) = 1 at hcomm
  simp only [map_mul,map_inv] at hcomm
  have hab : Commute (q a) (q b) := by
    change q a * q b = q b * q a
    calc
      _ = (q a * q b * (q a)⁻¹ * (q b)⁻¹) * (q b * q a) := by group
      _ = _ := by rw [hcomm,one_mul]
  have hu := freeGroup_heavy_commutes_all q hab u
  rcases hC with hC | hC
  · right
    rw [hC] at he
    have hq : q (b*a⁻¹) = 1 := by
      simp only [map_mul,map_inv]
      calc
        _ = q u * q b * (q u)⁻¹ * (q a)⁻¹ := by rw [hu.eq]; group
        _ = 1 := he
    exact (QuotientGroup.eq_one_iff _).mp hq
  · left
    rw [hC,map_inv] at he
    have hu' := hu.inv_right
    have hq : q b * q a = 1 := by
      have he' : (q b)⁻¹ * (q a)⁻¹ = 1 := by
        calc
          _ = q u * (q b)⁻¹ * (q u)⁻¹ * (q a)⁻¹ := by rw [hu'.eq]; group
          _ = 1 := he
      calc
        _ = ((q b)⁻¹ * (q a)⁻¹)⁻¹ := by rw [mul_inv_rev,inv_inv,inv_inv,hab.eq]
        _ = 1 := by rw [he',inv_one]
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b*a) = 1
    rw [map_mul,hq]

/-- It is enough to preserve short words up to the strictly smaller
threshold W+1, rather than the commutator's weight 2W+2. -/
theorem answer_of_heightStages_half_threshold
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (hshort : ∀ n w, w ∈ weightedHeightStage pick X n →
      weightedLength w ≤ 10^80 + 1 → w = 1) : answer := by
  apply answer_of_weightedStages pick X
  intro n hn
  have hb : weightedLength b = 10^80 := by simpa using weightedLength_b_zpow 1
  have ha : weightedLength a = 1 := by simpa using weightedLength_a_zpow 1
  have hai : weightedLength a⁻¹ = 1 := by
    simpa using weightedLength_a_zpow (-1)
  have hne : ∀ e : Bool, (if e then b*a else b*a⁻¹) ≠ 1 := by
    intro e h
    cases e
    · have h' : b*a⁻¹ = 1 := h
      have hba : b = a := by
        calc
          b = (b*a⁻¹)*a := by group
          _ = a := by rw [h',one_mul]
      rw [hba,ha] at hb
      norm_num at hb
    · have h' : b*a = 1 := h
      have hba : b = a⁻¹ := by
        calc
          b = (b*a)*a⁻¹ := by group
          _ = a⁻¹ := by rw [h',one_mul]
      rw [hba,hai] at hb
      norm_num at hb
  rcases weightedStages_comm_failure_shorter pick X n hn with h | h
  · apply hne true
    apply hshort n (b*a) _ _
    · rw [weightedHeightStage_eq]; exact h
    · have hle := weightedLength_mul_le b a
      omega
  · apply hne false
    apply hshort n (b*a⁻¹) _ _
    · rw [weightedHeightStage_eq]; exact h
    · have hle := weightedLength_mul_le b a⁻¹
      omega

#print axioms rawWord_at_most_heavy_weight
#print axioms heavy_not_good_bot
#print axioms initial_minBad_heavy
#print axioms freeGroup_heavy_commutes_all
#print axioms weightedStages_comm_failure_shorter
#print axioms answer_of_heightStages_half_threshold


/-- The first chosen period, which is defined independently of the
later stages and is one of the two signed heavy generators. -/
noncomputable def initialWeightedPeriod (pick : WeightedSelector) : F :=
  (pick ⊥ ⟨b,heavy_not_good_bot⟩).val

theorem initialWeightedPeriod_signed (pick : WeightedSelector) :
    initialWeightedPeriod pick = b ∨ initialWeightedPeriod pick = b⁻¹ :=
  initial_minBad_heavy _ (pick ⊥ ⟨b,heavy_not_good_bot⟩).property

/-- The first relation is available at every subsequent stage. -/
theorem initialWeightedPeriod_relation (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (hn : 1 ≤ n) :
    let C := initialWeightedPeriod pick
    let u := X 0 ⊥ C
    u*C*u⁻¹*a⁻¹ ∈ weightedStages pick X n := by
  intro C u
  apply weightedStages_mono pick X hn
  have hex : ∃ w : F, ¬ Good (⊥ : Subgroup F) w := ⟨b,heavy_not_good_bot⟩
  change u*C*u⁻¹*a⁻¹ ∈ adjoin ⊥ (weightedRelator pick X 0 ⊥)
  have hC : C = (pick ⊥ hex).val := rfl
  have hu : u = X 0 ⊥ C := rfl
  rw [weightedRelator_eq pick X 0 ⊥ hex,heightRelator_one,hu,hC]
  exact relator_mem_adjoin _ _

/-- For a quotient which already contains the first defining relation,
survival of the commutator is EXACTLY survival of a single fixed
two-letter word. No metric hypotheses or later geometric estimates
are involved in the equivalence. -/
theorem commWord_mem_iff_initial_period_mem
    (N : Subgroup F) [N.Normal] (C u : F)
    (hC : C = b ∨ C = b⁻¹)
    (hrel : u*C*u⁻¹*a⁻¹ ∈ N) :
    commWord ∈ N ↔ C*a⁻¹ ∈ N := by
  let q := QuotientGroup.mk' N
  have hc : q (u*C*u⁻¹*a⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hrel
  constructor
  · intro hm
    have he : q commWord = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    change q (a*b*a⁻¹*b⁻¹) = 1 at he
    simp only [map_mul,map_inv] at he
    have hab : Commute (q a) (q b) := by
      change q a * q b = q b * q a
      calc
        _ = (q a*q b*(q a)⁻¹*(q b)⁻¹)*(q b*q a) := by group
        _ = _ := by rw [he,one_mul]
    have hu := freeGroup_heavy_commutes_all q hab u
    have huc : Commute (q u) (q C) := by
      rcases hC with h | h
      · rw [h]
        exact hu
      · rw [h,map_inv]
        exact hu.inv_right
    apply (QuotientGroup.eq_one_iff _).mp
    change q (C*a⁻¹) = 1
    simp only [map_mul,map_inv] at hc ⊢
    calc
      _ = q u*q C*(q u)⁻¹*(q a)⁻¹ := by rw [huc.eq]; group
      _ = 1 := hc
  · intro hm
    have he : q (C*a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    simp only [map_mul,map_inv] at he
    have hca : q C = q a := by
      calc
        _ = (q C*(q a)⁻¹)*q a := by group
        _ = _ := by rw [he,one_mul]
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a*b*a⁻¹*b⁻¹) = 1
    simp only [map_mul,map_inv]
    rcases hC with h | h
    · rw [h] at hca
      rw [hca]
      group
    · rw [h,map_inv] at hca
      have hb : q b = (q a)⁻¹ := by
        rw [← hca,inv_inv]
      rw [hb]
      group

theorem weightedStages_comm_iff_initial_period
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (hn : 1 ≤ n) :
    commWord ∈ weightedStages pick X n ↔
      initialWeightedPeriod pick*a⁻¹ ∈ weightedStages pick X n := by
  let N := weightedStages pick X n
  let : N.Normal := weightedStages_normal pick X n
  exact commWord_mem_iff_initial_period_mem N (initialWeightedPeriod pick)
    (X 0 ⊥ (initialWeightedPeriod pick)) (initialWeightedPeriod_signed pick)
    (initialWeightedPeriod_relation pick X n hn)

/-- The exact Kourovka target now needs only the survival of one
specific word, fixed before the entire recursive process starts.
It does not require any injectivity ball, torsion-freeness or survival
of other pure powers of the light generator. -/
theorem answer_of_initial_period_survival (pick : WeightedSelector)
    (X : ConjugatorChoice)
    (hsurvive : ∀ n ≥ 1,
      initialWeightedPeriod pick*a⁻¹ ∉ weightedStages pick X n) : answer := by
  apply answer_of_weightedStages pick X
  intro n hn
  by_cases h : 1 ≤ n
  · exact hsurvive n h ((weightedStages_comm_iff_initial_period pick X n h).mp hn)
  · have h0 : n = 0 := by omega
    subst n
    exact commWord_ne_one hn

#print axioms initialWeightedPeriod_signed
#print axioms initialWeightedPeriod_relation
#print axioms commWord_mem_iff_initial_period_mem
#print axioms weightedStages_comm_iff_initial_period
#print axioms answer_of_initial_period_survival


/-! ## Direct nonabelian certificate for the first positive period

This is an independent algebraic base case, not a graded overlap
argument. The certificate is a permutation representation over the
algebraic closure of the rationals. Only the initial four letters
of the conjugating word are used.
-/

/-- Fixed-point polynomial of a positive word in two affine maps
with common multiplier T and respective fixed points 0 and 1. -/
noncomputable def affineFixedPolynomial (K : Type) [Field K] :
    List (Fin 2) → Polynomial K
  | [] => 1
  | i :: xs => Polynomial.X * affineFixedPolynomial K xs +
      (if i = 0 then 0 else 1 - Polynomial.X)

theorem affineFixedPolynomial_eval_one (K : Type) [Field K]
    (xs : List (Fin 2)) :
    (affineFixedPolynomial K xs).eval 1 = 1 := by
  induction xs with
  | nil => simp [affineFixedPolynomial]
  | cons i xs ih =>
    fin_cases i <;> simp [affineFixedPolynomial,ih]

theorem affineFixedPolynomial_prefix (K : Type) [Field K]
    (xs : List (Fin 2)) :
    affineFixedPolynomial K (1::1::1::0::xs) =
      1 - Polynomial.X^3 + Polynomial.X^4 * affineFixedPolynomial K xs := by
  norm_num [affineFixedPolynomial]
  ring

/-- The prefix bbba forces a nonconstant polynomial with no roots
at zero or one. Algebraic closure supplies a suitable multiplier. -/
theorem affineFixedPolynomial_root (xs : List (Fin 2)) :
    ∃ t : AlgebraicClosure ℚ, t ≠ 0 ∧ t ≠ 1 ∧
      (affineFixedPolynomial (AlgebraicClosure ℚ) (1::1::1::0::xs)).eval t = 0 := by
  let K := AlgebraicClosure ℚ
  let p := affineFixedPolynomial K (1::1::1::0::xs)
  have h3 : p.coeff 3 = -1 := by
    change (affineFixedPolynomial K (1::1::1::0::xs)).coeff 3 = _
    rw [affineFixedPolynomial_prefix]
    norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,
      Polynomial.coeff_X_pow,Polynomial.coeff_X_pow_mul',Polynomial.coeff_one]
  have hdeg : p.degree ≠ 0 := by
    intro h
    have hp := Polynomial.eq_C_of_degree_eq_zero h
    rw [hp] at h3
    norm_num at h3
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_root p hdeg
  change p.eval t = 0 at ht
  refine ⟨t,?_,?_,ht⟩
  · intro he
    rw [he] at ht
    change (affineFixedPolynomial K (1::1::1::0::xs)).eval 0 = 0 at ht
    rw [affineFixedPolynomial_prefix] at ht
    norm_num at ht
  · intro he
    rw [he] at ht
    change (affineFixedPolynomial K (1::1::1::0::xs)).eval 1 = 0 at ht
    rw [affineFixedPolynomial_eval_one] at ht
    exact one_ne_zero ht

/-- The affine bijection x ↦ t*x+s. -/
def affinePerm {K : Type} [Field K] (t s : K) (ht : t ≠ 0) :
    Equiv.Perm K where
  toFun x := t*x+s
  invFun y := (y-s)/t
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring

def affineFreeMap {K : Type} [Field K] (t : K) (ht : t ≠ 0) :
    F →* Equiv.Perm K :=
  FreeGroup.lift (fun i => affinePerm t (if i = 0 then 0 else 1-t) ht)

theorem affineFreeMap_a {K : Type} [Field K] (t : K) (ht : t ≠ 0) (x : K) :
    affineFreeMap t ht a x = t*x := by
  simp [affineFreeMap,a,FreeGroup.lift_apply_of,affinePerm]

theorem affineFreeMap_b {K : Type} [Field K] (t : K) (ht : t ≠ 0) (x : K) :
    affineFreeMap t ht b x = t*x+1-t := by
  simp [affineFreeMap,b,FreeGroup.lift_apply_of,affinePerm]; ring

/-- The polynomial evaluates the image of 1; the full affine
function is determined by its multiplier and this value. -/
theorem affineFreeMap_positive {K : Type} [Field K] (t : K) (ht : t ≠ 0)
    (xs : List (Fin 2)) (x : K) :
    affineFreeMap t ht (positiveWord xs) x =
      t^xs.length*(x-1)+(affineFixedPolynomial K xs).eval t := by
  induction xs with
  | nil =>
    have he : positiveWord [] = 1 := rfl
    rw [he,map_one]
    simp [affineFixedPolynomial]
  | cons i xs ih =>
    have he : positiveWord (i::xs) = FreeGroup.of i * positiveWord xs := by
      change FreeGroup.mk ((i,true)::xs.map (fun j => (j,true))) =
        FreeGroup.of i * FreeGroup.mk (xs.map (fun j => (j,true)))
      rw [← FreeGroup.mk_eq_of,FreeGroup.mul_mk]
      rfl
    rw [he,map_mul,Equiv.Perm.mul_apply]
    change (affineFreeMap t ht (FreeGroup.of i))
      (affineFreeMap t ht (positiveWord xs) x) = _
    rw [ih]
    fin_cases i
    · change affineFreeMap t ht a _ = _
      rw [affineFreeMap_a]
      simp [affineFixedPolynomial,List.length_cons,pow_succ]
      ring
    · change affineFreeMap t ht b _ = _
      rw [affineFreeMap_b]
      simp [affineFixedPolynomial,List.length_cons,pow_succ]
      ring

/-- If X begins bbba, the relator X b X^-1 a^-1 has an explicit
nonabelian quotient. In particular b*a^-1 is not in its normal
closure. No assumption about diagram minimality is needed. -/
theorem first_positive_relator_survival (xs : List (Fin 2)) :
    let X := positiveWord (1::1::1::0::xs)
    b*a⁻¹ ∉ adjoin ⊥ (X*b*X⁻¹*a⁻¹) := by
  intro X hm
  obtain ⟨t,ht0,ht1,hroot⟩ := affineFixedPolynomial_root xs
  let q := affineFreeMap t ht0
  have hX (x : AlgebraicClosure ℚ) : q X x =
      t^(1::1::1::0::xs : List (Fin 2)).length*(x-1) := by
    have h := affineFreeMap_positive t ht0 (1::1::1::0::xs) x
    rw [hroot,add_zero] at h
    exact h
  have halign : q X * q b = q a * q X := by
    ext x
    simp only [Equiv.Perm.mul_apply]
    rw [hX,affineFreeMap_b,affineFreeMap_a,hX]
    ring
  have hrel : q (X*b*X⁻¹*a⁻¹) = 1 := by
    simp only [map_mul,map_inv]
    rw [halign]
    group
  have hker : adjoin ⊥ (X*b*X⁻¹*a⁻¹) ≤ q.ker := by
    unfold adjoin
    apply Subgroup.normalClosure_le_normal
    intro w hw
    rcases hw with h | h
    · have hw1 : w = 1 := h
      rw [hw1]
      exact q.ker.one_mem
    · have hw1 : w = X*b*X⁻¹*a⁻¹ := h
      subst w
      exact hrel
  have he : q (b*a⁻¹) = 1 := hker hm
  simp only [map_mul,map_inv] at he
  have hb : q b = q a := by
    calc
      _ = (q b*(q a)⁻¹)*q a := by group
      _ = _ := by rw [he,one_mul]
  have h0 := congrArg (fun f : Equiv.Perm (AlgebraicClosure ℚ) => f 0) hb
  change q b 0 = q a 0 at h0
  rw [affineFreeMap_b,affineFreeMap_a] at h0
  apply ht1
  linear_combination -h0

#print axioms affineFixedPolynomial_eval_one
#print axioms affineFixedPolynomial_prefix
#print axioms affineFixedPolynomial_root
#print axioms affineFreeMap_a
#print axioms affineFreeMap_b
#print axioms affineFreeMap_positive
#print axioms first_positive_relator_survival


/-! ## Obstruction to solving the entire problem by abelian-kernel
representations. These results explain why an affine certificate
for rank one cannot simply be kept unchanged at every rank. -/

/-- If a group is covered by conjugates of a cyclic subgroup and
is cyclic modulo an abelian normal subgroup, then it is cyclic
in the stronger sense that every element is already a power of A. -/
theorem cyclic_cover_abelian_kernel_collapse {K : Type} [Group K]
    (N : Subgroup K) [N.Normal] (A : K)
    (hab : ∀ x ∈ N, ∀ y ∈ N, Commute x y)
    (hmod : ∀ g : K, ∃ m : ℤ, g * (A^m)⁻¹ ∈ N)
    (hcover : ∀ g : K, ∃ (u : K) (k : ℤ), u*g*u⁻¹ = A^k) :
    ∀ g : K, ∃ k : ℤ, g = A^k := by
  have hcentral (k : ℤ) (hk : A^k ∈ N) (g : K) :
      Commute g (A^k) := by
    obtain ⟨m,hm⟩ := hmod g
    have h1 := hab (g*(A^m)⁻¹) hm (A^k) hk
    have h2 : Commute (A^m) (A^k) :=
      (Commute.refl A).zpow_zpow m k
    have h := h1.mul_left h2
    have he : (g*(A^m)⁻¹)*A^m = g := by group
    rwa [he] at h
  have hn (g : K) (hg : g ∈ N) : ∃ k : ℤ, g = A^k := by
    obtain ⟨u,k,he⟩ := hcover g
    have hk : A^k ∈ N := by
      rw [← he]
      exact (inferInstance : N.Normal).conj_mem g hg u
    have hc := (hcentral k hk u).eq
    refine ⟨k,?_⟩
    calc
      g = u⁻¹*(u*g*u⁻¹)*u := by group
      _ = u⁻¹*(A^k)*u := by rw [he]
      _ = A^k := by
        calc
          _ = u⁻¹*((A^k)*u) := by group
          _ = u⁻¹*(u*(A^k)) := by rw [hc]
          _ = A^k := by group
  intro g
  obtain ⟨m,hm⟩ := hmod g
  obtain ⟨k,hk⟩ := hn _ hm
  refine ⟨k+m,?_⟩
  calc
    g = (g*(A^m)⁻¹)*A^m := by group
    _ = A^k*A^m := by rw [hk]
    _ = A^(k+m) := (zpow_add A k m).symm

/-- For a normal subgroup containing the conjugacy relation for
the commutator, a representation whose distinguished generator
has faithful powers under a character cannot detect that commutator.
The character target is abelian; the representation target need
not be abelian. -/
theorem character_obstruction_to_commutator_survival
    {K L : Type} [Group K] [CommGroup L]
    (N : Subgroup F) (q : F →* K) (chi : K →* L)
    (hker : N ≤ q.ker)
    (hgood : Good N commWord)
    (hfaith : ∀ k : ℤ, chi ((q a)^k) = 1 → (q a)^k = 1) :
    q commWord = 1 := by
  obtain ⟨u,k,hu⟩ := hgood
  have hrel : q (u*commWord*u⁻¹*(a^k)⁻¹) = 1 := hker hu
  have he : q u*q commWord*(q u)⁻¹ = (q a)^k := by
    simp only [map_mul,map_inv,map_zpow] at hrel
    calc
      _ = (q u*q commWord*(q u)⁻¹*((q a)^k)⁻¹)*(q a)^k := by group
      _ = _ := by rw [hrel,one_mul]
  have hchi : chi (q commWord) = 1 := by
    change chi (q (a*b*a⁻¹*b⁻¹)) = 1
    simp only [map_mul,map_inv]
    rw [mul_comm (chi (q a)) (chi (q b))]
    group
  have hc := congrArg chi he
  simp only [map_mul,map_inv,hchi,mul_one,mul_inv_cancel] at hc
  have hpow := hfaith k hc.symm
  calc
    q commWord = (q u)⁻¹*(q u*q commWord*(q u)⁻¹)*q u := by group
    _ = _ := by rw [he,hpow]; group

/-- There is a finite rank beyond which every representation with
the above character property kills the commutator, regardless of
the conjugator choice. The bound depends on the actual greedy chain,
not on the representation or its target group. -/
theorem eventually_character_obstruction (pick : WeightedSelector)
    (X : ConjugatorChoice) :
    ∃ n : ℕ, ∀ m ≥ n, ∀ (K L : Type) [Group K] [CommGroup L]
      (q : F →* K) (chi : K →* L),
      weightedStages pick X m ≤ q.ker →
      (∀ k : ℤ, chi ((q a)^k) = 1 → (q a)^k = 1) →
      q commWord = 1 := by
  obtain ⟨n,hn⟩ := weightedStages_cover pick X commWord
  refine ⟨n,?_⟩
  intro m hm K L iK iL q chi hker hfaith
  exact character_obstruction_to_commutator_survival
    (weightedStages pick X m) q chi hker
    (good_mono (weightedStages_mono pick X hm) hn) hfaith

#print axioms cyclic_cover_abelian_kernel_collapse
#print axioms character_obstruction_to_commutator_survival
#print axioms eventually_character_obstruction


/-- A character which detects every nonzero exponent of a rules
out goodness of any nonidentity word of zero character. -/
theorem zero_character_bad {K : Type} [CommGroup K] (N : Subgroup F) [N.Normal]
    (q : F →* K) (hker : N ≤ q.ker)
    (ha : ∀ k : ℤ, (q a)^k = 1 → k = 0)
    (w : F) (hw : w ∉ N) (hzero : q w = 1) :
    ¬ Good N w := by
  rintro ⟨u,k,hu⟩
  have he : q (u*w*u⁻¹*(a^k)⁻¹) = 1 := hker hu
  simp only [map_mul,map_inv,map_zpow,hzero,mul_one,mul_inv_cancel,one_mul] at he
  have hk : k = 0 := ha k (inv_eq_one.mp he)
  subst k
  simp only [zpow_zero,inv_one,mul_one] at hu
  have h := (inferInstance : N.Normal)
  -- Normality is needed only to remove the conjugator.
  apply hw
  have hh := h.conj_mem _ hu u⁻¹
  have he : u⁻¹ * (u*w*u⁻¹) * (u⁻¹)⁻¹ = w := by group
  rwa [he] at hh

/-- At the first positive rank, b*a^-1 is a minimal bad period
as soon as it survives. The abelian character sends both generators
to the same infinite-order element. -/
theorem first_positive_second_minBad (u : F)
    (hw : b*a⁻¹ ∉ adjoin ⊥ (u*b*u⁻¹*a⁻¹)) :
    MinBad (adjoin ⊥ (u*b*u⁻¹*a⁻¹)) (b*a⁻¹) := by
  let N := adjoin ⊥ (u*b*u⁻¹*a⁻¹)
  let q : F →* Multiplicative ℤ := FreeGroup.lift (fun _ => Multiplicative.ofAdd 1)
  have ha : q a = Multiplicative.ofAdd 1 := by
    simp [q,a,FreeGroup.lift_apply_of]
  have hb : q b = Multiplicative.ofAdd 1 := by
    simp [q,b,FreeGroup.lift_apply_of]
  have hker : N ≤ q.ker := by
    unfold N adjoin
    apply Subgroup.normalClosure_le_normal
    intro w hw'
    rcases hw' with h | h
    · have he : w = 1 := h
      rw [he]
      exact q.ker.one_mem
    · have he : w = u*b*u⁻¹*a⁻¹ := h
      change q w = 1
      rw [he]
      simp only [map_mul,map_inv,ha,hb]
      rw [mul_comm (q u) (Multiplicative.ofAdd 1),mul_assoc (Multiplicative.ofAdd 1),
        mul_inv_cancel,mul_one,mul_inv_cancel]
  have hbad : ¬ Good N (b*a⁻¹) := by
    have hf : ∀ k : ℤ, (q a)^k = 1 → k = 0 := by
      intro k hk
      rw [ha] at hk
      change k * 1 = 0 at hk
      omega
    have hzero : q (b*a⁻¹) = 1 := by
      rw [map_mul,map_inv,hb,ha,mul_inv_cancel]
    exact zero_character_bad N q hker hf _ hw hzero
  have hbGood : Good N b := by
    refine ⟨u,1,?_⟩
    rw [zpow_one]
    exact relator_mem_adjoin _ _
  have hbiGood : Good N b⁻¹ := by
    simpa only [zpow_neg_one] using good_integer_power N hbGood (-1)
  refine ⟨hbad,?_⟩
  intro w h
  by_contra! hlt
  have hbw : weightedLength b = 10^80 := by simpa using weightedLength_b_zpow 1
  have hai : weightedLength a⁻¹ = 1 := by simpa using weightedLength_a_zpow (-1)
  have hle := weightedLength_mul_le b a⁻¹
  have hsmall : rawWeight w.toWord ≤ 10^80 := by
    change weightedLength w ≤ _
    omega
  have hc := rawWord_at_most_heavy_weight w.toWord hsmall
  rw [FreeGroup.mk_toWord] at hc
  rcases hc with ⟨k,hk⟩ | hk | hk
  · exact h (hk.symm ▸ good_a_zpow N k)
  · exact h (hk.symm ▸ hbGood)
  · exact h (hk.symm ▸ hbiGood)

/-- Giving priority to b and then b*a^-1 among weight-minimal bad
words is legitimate at every stage. The second branch is reached
after the first positive relation whenever b*a^-1 survives. -/
noncomputable def twoPeriodSelector : WeightedSelector := by
  classical
  intro N h
  exact if hb : MinBad N b then ⟨b,hb⟩
    else if hd : MinBad N (b*a⁻¹) then ⟨b*a⁻¹,hd⟩
    else arbitraryWeightedSelector N h

theorem twoPeriodSelector_first (h : ∃ w : F, ¬ Good (⊥ : Subgroup F) w) :
    (twoPeriodSelector ⊥ h).val = b := by
  have hb : MinBad (⊥ : Subgroup F) b := by
    refine ⟨heavy_not_good_bot,?_⟩
    intro w hw
    have hweight := weight_ge_of_bad _ _ hw
    have hbw : weightedLength b = 10^80 := by simpa using weightedLength_b_zpow 1
    rwa [hbw]
  simp only [twoPeriodSelector,dite_eq_left hb]

theorem twoPeriodSelector_second (u : F)
    (hw : b*a⁻¹ ∉ adjoin ⊥ (u*b*u⁻¹*a⁻¹))
    (h : ∃ w : F, ¬ Good (adjoin ⊥ (u*b*u⁻¹*a⁻¹)) w) :
    (twoPeriodSelector (adjoin ⊥ (u*b*u⁻¹*a⁻¹)) h).val = b*a⁻¹ := by
  have hg : Good (adjoin ⊥ (u*b*u⁻¹*a⁻¹)) b := by
    refine ⟨u,1,?_⟩
    rw [zpow_one]
    exact relator_mem_adjoin _ _
  have hb : ¬ MinBad (adjoin ⊥ (u*b*u⁻¹*a⁻¹)) b := fun h => h.1 hg
  simp only [twoPeriodSelector,dite_eq_right hb,dite_eq_left (first_positive_second_minBad u hw)]

/-- Two explicit conjugacy relations already imply that if the
distinguished generator survives, the commutator survives too.
This holds regardless of every subsequently imposed relation. -/
theorem two_period_noncollapse (N : Subgroup F) [N.Normal]
    (u v : F) (h1 : u*b*u⁻¹*a⁻¹ ∈ N)
    (h2 : v*(b*a⁻¹)*v⁻¹*a⁻¹ ∈ N)
    (ha : a ∉ N) : commWord ∉ N := by
  intro hc
  have hd : b*a⁻¹ ∈ N :=
    (commWord_mem_iff_initial_period_mem N b u (Or.inl rfl) h1).mp hc
  let q := QuotientGroup.mk' N
  have hq : q (b*a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hd
  have hr : q (v*(b*a⁻¹)*v⁻¹*a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h2
  have hq' : q v*q (b*a⁻¹)*(q v)⁻¹*(q a)⁻¹ = 1 := by
    simpa only [map_mul,map_inv] using hr
  rw [hq,mul_one,mul_inv_cancel,one_mul] at hq'
  exact ha ((QuotientGroup.eq_one_iff _).mp (inv_eq_one.mp hq'))

#print axioms zero_character_bad
#print axioms first_positive_second_minBad
#print axioms twoPeriodSelector_first
#print axioms twoPeriodSelector_second
#print axioms two_period_noncollapse


/-- Every actual long conjugating word begins with the four-letter
prefix needed by the independent affine base-case certificate. -/
theorem guba_longRaw_bbba (m : ℕ) :
    ∃ xs : List (Fin 2), longRaw (gubaEvenPrefix m) (10^20) =
      1::1::1::0::xs := by
  let q := gubaEvenPrefix m
  have hhead : q[0]? = some 0 := gubaPrefix_head_zero (2*m+1)
  obtain ⟨u,hu⟩ : ∃ u, q = 0::u := by
    cases hq : q with
    | nil => simp [hq] at hhead
    | cons i is =>
      have hi : i = 0 := by simpa only [hq,List.getElem?_cons_zero,Option.some.injEq] using hhead
      exact ⟨is,by rw [hi]⟩
  obtain ⟨v,hv⟩ := List.prefix_iff_exists_append_eq.mp
    (longRaw_prefix q (show 1 ≤ (10^20 : ℕ) by norm_num))
  refine ⟨u++v,?_⟩
  rw [← hv]
  simp [longRaw,longBlock,hu]

/-- In the specialized greedy chain the first stage is exactly the
positive single-relator presentation; its two-letter difference
survives by the affine certificate. -/
theorem guba_twoPeriod_first_stage :
    let pick := twoPeriodSelector
    let X := gubaConjugatorChoice pick
    let u := X 0 ⊥ b
    weightedStages pick X 1 = adjoin ⊥ (u*b*u⁻¹*a⁻¹) ∧
      b*a⁻¹ ∉ weightedStages pick X 1 := by
  intro pick X u
  have h0 : ∃ w : F, ¬ Good (⊥ : Subgroup F) w := ⟨b,heavy_not_good_bot⟩
  have hfirst : (pick ⊥ h0).val = b := twoPeriodSelector_first h0
  have hstage : weightedStages pick X 1 = adjoin ⊥ (u*b*u⁻¹*a⁻¹) := by
    change adjoin ⊥ (weightedRelator pick X 0 ⊥) = _
    rw [weightedRelator_eq pick X 0 ⊥ h0,hfirst,heightRelator_one]
  refine ⟨hstage,?_⟩
  rw [hstage]
  obtain ⟨xs,hxs⟩ := guba_longRaw_bbba (chooseEvenPrefixIndex b (gubaState pick 0).2)
  have hu : u = positiveWord (1::1::1::0::xs) := by
    change positiveWord (longRaw
      (gubaEvenPrefix (chooseEvenPrefixIndex b (gubaState pick 0).2)) (10^20)) = _
    rw [hxs]
  rw [hu]
  exact first_positive_relator_survival xs

/-- The actual first two defining relations with the prescribed
selector, not arbitrary additional relations inserted into the
recursive process. -/
theorem guba_twoPeriod_relations (n : ℕ) (hn : 2 ≤ n) :
    let pick := twoPeriodSelector
    let X := gubaConjugatorChoice pick
    let N := weightedStages pick X n
    let u := X 0 ⊥ b
    let v := X 1 (weightedStages pick X 1) (b*a⁻¹)
    u*b*u⁻¹*a⁻¹ ∈ N ∧ v*(b*a⁻¹)*v⁻¹*a⁻¹ ∈ N := by
  intro pick X N u v
  obtain ⟨hstage,hsurv⟩ := guba_twoPeriod_first_stage
  change weightedStages pick X 1 = adjoin ⊥ (u*b*u⁻¹*a⁻¹) at hstage
  change b*a⁻¹ ∉ weightedStages pick X 1 at hsurv
  have hmin : MinBad (weightedStages pick X 1) (b*a⁻¹) := by
    rw [hstage]
    exact first_positive_second_minBad u (by rw [← hstage]; exact hsurv)
  have hex : ∃ w : F, ¬ Good (weightedStages pick X 1) w := ⟨_,hmin.1⟩
  have hchoose : (pick (weightedStages pick X 1) hex).val = b*a⁻¹ := by
    -- Avoid transporting dependent witnesses across subgroup equalities.
    have hb : Good (weightedStages pick X 1) b := by
      rw [hstage]
      refine ⟨u,1,?_⟩
      rw [zpow_one]
      exact relator_mem_adjoin _ _
    have hnb : ¬ MinBad (weightedStages pick X 1) b := fun h => h.1 hb
    change (twoPeriodSelector (weightedStages pick X 1) hex).val = _
    simp only [twoPeriodSelector,dite_eq_right hnb,dite_eq_left hmin]
  constructor
  · apply weightedStages_mono pick X (show 1 ≤ n by omega)
    rw [hstage]
    exact relator_mem_adjoin _ _
  · apply weightedStages_mono pick X hn
    change v*(b*a⁻¹)*v⁻¹*a⁻¹ ∈ adjoin (weightedStages pick X 1)
      (weightedRelator pick X 1 (weightedStages pick X 1))
    rw [weightedRelator_eq pick X 1 _ hex,hchoose,heightRelator_one]
    exact relator_mem_adjoin _ _

/-- It suffices to exclude the disappearance of the single letter a
from the actual specialized greedy presentation. -/
theorem answer_of_guba_one_letter_survival
    (hsurv : ∀ n, a ∉ weightedHeightStage twoPeriodSelector
      (gubaConjugatorChoice twoPeriodSelector) n) : answer := by
  let pick := twoPeriodSelector
  let X := gubaConjugatorChoice pick
  apply answer_of_weightedStages pick X
  intro n hc
  let N := weightedStages pick X (max 2 n)
  let : N.Normal := weightedStages_normal pick X (max 2 n)
  obtain ⟨h1,h2⟩ := guba_twoPeriod_relations (max 2 n) (le_max_left _ _)
  have ha : a ∉ N := by
    change a ∉ weightedStages pick X (max 2 n)
    rw [← weightedHeightStage_eq]
    exact hsurv _
  exact (two_period_noncollapse N _ _ h1 h2 ha)
    (weightedStages_mono pick X (le_max_right _ _) hc)

/-- The geometric obligation is now an actual connected marked
ribbon with exactly one outer dart, with positive rank-minimal
interior occurrences. No uniform perimeter hypothesis is used. -/
theorem answer_of_guba_one_dart_step
    (step : ∀ j (s : Peiffer.Sequence F (RankHeight (j+1)))
      (hs : Peiffer.evaluation
        (fun i => FreeGroup.mk (rankHeightRows twoPeriodSelector
          (gubaConjugatorChoice twoPeriodSelector) (j+1) i)) s = a),
      a ∉ weightedHeightStage twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) j →
      RankMinimalExpression twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) (j+1) a s →
      (∀ x ∈ s, x.2 = true) →
      let rows := rankHeightRows twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) (j+1)
      let P := boundaryRibbon rows a s hs
      let z := boundaryDart rows a s (show a ≠ 1 by
        intro h
        have hw : weightedLength a = 1 := by simpa using weightedLength_a_zpow 1
        rw [h] at hw
        have hz := (weightedLength_eq_zero_iff (1 : F)).mpr rfl
        omega)
      P.Connected → P.EulerEquality → P.vertexBoundary z = [z] → False) :
    answer := by
  have ha : a ≠ 1 := by
    intro h
    have hw : weightedLength a = 1 := by simpa using weightedLength_a_zpow 1
    rw [h] at hw
    have hz := (weightedLength_eq_zero_iff (1 : F)).mpr rfl
    omega
  apply answer_of_guba_one_letter_survival
  intro n
  induction n with
  | zero =>
    intro h
    rw [weightedHeightStage_eq] at h
    exact ha h
  | succ j ih =>
    intro h
    let pick := twoPeriodSelector
    let X := gubaConjugatorChoice pick
    obtain ⟨s,hm,hpos,hs,hE⟩ := exists_rankMinimal_ribbon_expression pick X (j+1) a h
    let rows := rankHeightRows pick X (j+1)
    let P := boundaryRibbon rows a s hs
    let z := boundaryDart rows a s ha
    have hc : P.Connected := guba23_rankMinimal_ribbon_connected pick X (j+1) a s hm ha hs
    have hr := boundaryRibbon_read rows a s hs ha
    have haWord : a.toWord = ([(0,true)] : RawWord) := by decide
    rw [haWord] at hr
    have hlen := congrArg List.length hr
    rw [List.length_map,FreeGroup.invRev_length] at hlen
    obtain ⟨l,hl⟩ := cycleBoundary_cons P.rotation z
    change P.vertexBoundary z = z::l at hl
    have hnil : l = [] := by
      apply List.length_eq_zero_iff.mp
      rw [hl,List.length_cons] at hlen
      simp only [List.length_singleton] at hlen
      omega
    exact step j s hs ih hm hpos hc hE (by rw [hl,hnil])

#print axioms guba_longRaw_bbba
#print axioms guba_twoPeriod_first_stage
#print axioms guba_twoPeriod_relations
#print axioms answer_of_guba_one_letter_survival
#print axioms answer_of_guba_one_dart_step


/-- A one-dart vertex is a genuine leaf: its unique edge leaves
the vertex, and no other dart lies in the marked vertex cycle. -/
theorem oneDart_leaf {D : Type} [Fintype D] (P : RibbonMap D)
    (z : D) (hz : P.vertexBoundary z = [z]) :
    P.rotation z = z ∧
      (∀ d, P.rotation.SameCycle z d ↔ d = z) ∧
      ¬ P.rotation.SameCycle z (P.edge z) := by
  have hcyc (d : D) : P.rotation.SameCycle z d ↔ d = z := by
    rw [← P.mem_vertexBoundary_iff,hz,List.mem_singleton]
  have hfix : P.rotation z = z :=
    (hcyc _).mp (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  refine ⟨hfix,hcyc,?_⟩
  intro h
  exact P.edge_ne z ((hcyc _).mp h)

/-- Removing the leaf edge transfers the boundary to the unique
adjacent cell, with its initial letter deleted. The resulting
defect word lies in any normal subgroup containing the readings
of every other cell. This is an actual ribbon surgery, not an
assumed contiguity estimate. -/
theorem oneDart_adjacent_cell_defect {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter)
    (N : Subgroup F) [N.Normal] (z : D)
    (hz : P.vertexBoundary z = [z])
    (hE : P.EulerEquality)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d))
    (hint : ∀ d, P.SameComponent z d →
      ¬ P.rotation.SameCycle z d →
      ¬ P.rotation.SameCycle (P.edge z) d →
      FreeGroup.mk ((P.vertexBoundary d).map read) ∈ N) :
    ∃ l : List D, P.vertexBoundary (P.edge z) = P.edge z::l ∧
      FreeGroup.mk (l.map read) ∈ N ∧
      rawWeight ((P.vertexBoundary (P.edge z)).map read) =
        letterWeight (read (P.edge z)) + rawWeight (l.map read) := by
  obtain ⟨hfix,_,hn⟩ := oneDart_leaf P z hz
  obtain ⟨l,hl⟩ := cycleBoundary_cons P.rotation (P.edge z)
  change P.vertexBoundary (P.edge z) = P.edge z::l at hl
  have hm := edgeSplice_boundary_mem_normal P read N z hn hE hedge hint
  rw [hfix,hz,hl] at hm
  change FreeGroup.mk ([read z,read (P.edge z)] ++ l.map read) ∈ N at hm
  have hcancel : FreeGroup.mk [read z,read (P.edge z)] = 1 := by
    rw [hedge]
    change FreeGroup.mk ([read z] ++ [reverseLetter (read z)]) = 1
    rw [← FreeGroup.mul_mk,signedLetterValue_reverse,mul_inv_cancel]
  rw [← FreeGroup.mul_mk,hcancel,one_mul] at hm
  refine ⟨l,hl,hm,?_⟩
  rw [hl,List.map_cons,rawWeight]

/-- In particular the defective cyclic cell word belongs to the
normal closure of the readings of all remaining interior cells.
This removes one whole cell from the normal generation problem
and specifies the new boundary literally. -/
theorem oneDart_defect_generated_by_other_cells {D : Type} [Fintype D]
    (P : RibbonMap D) (read : D → Letter) (z : D)
    (hz : P.vertexBoundary z = [z])
    (hE : P.EulerEquality)
    (hedge : ∀ d, read (P.edge d) = reverseLetter (read d)) :
    ∃ l : List D, P.vertexBoundary (P.edge z) = P.edge z::l ∧
      FreeGroup.mk (l.map read) ∈ Subgroup.normalClosure
        {w : F | ∃ d, P.SameComponent z d ∧
          ¬ P.rotation.SameCycle z d ∧
          ¬ P.rotation.SameCycle (P.edge z) d ∧
          w = FreeGroup.mk ((P.vertexBoundary d).map read)} := by
  let N := Subgroup.normalClosure
    {w : F | ∃ d, P.SameComponent z d ∧
      ¬ P.rotation.SameCycle z d ∧
      ¬ P.rotation.SameCycle (P.edge z) d ∧
      w = FreeGroup.mk ((P.vertexBoundary d).map read)}
  let : N.Normal := by
    unfold N
    infer_instance
  obtain ⟨l,hl,hm,_⟩ := oneDart_adjacent_cell_defect P read N z hz hE hedge
    (fun d hc h1 h2 => Subgroup.subset_normalClosure ⟨d,hc,h1,h2,rfl⟩)
  exact ⟨l,hl,hm⟩

#print axioms oneDart_leaf
#print axioms oneDart_adjacent_cell_defect
#print axioms oneDart_defect_generated_by_other_cells


/-- The defect obtained by merging the single outer dart into its
adjacent cell has a filling of strictly smaller rank type. Every
remaining factor has a distinct original occurrence index. Reinsert the
omitted cell to recover the original boundary and exact rank profile;
for a minimal parent, the actual remaining expression is minimal. -/
theorem oneDart_rankMinimal_defect_exact_type
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (hw : w ≠ 1) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    P.Connected → P.vertexBoundary z = [z] →
    ∃ l : List _, P.vertexBoundary (P.edge z) = P.edge z::l ∧
      ∃ (i : Fin s.length) (y : Peiffer.Occurrence F (RankHeight n))
        (t : Peiffer.Sequence F (RankHeight n)),
        y.1.2 = s[i.val].1.2 ∧
        Peiffer.evaluation (rankHeightRel pick X n) t =
          (FreeGroup.mk (l.map read))⁻¹ ∧
        Peiffer.evaluation (rankHeightRel pick X n) (y::t) = w ∧
        descendingCountLT n rankCount t s ∧
        (discOccurrence (markedRows rows w) (boundaryIdentity s)
          (P.edge z)).val = i.val+1 ∧
        Peiffer.term (rankHeightRel pick X n) y = w * FreeGroup.mk (l.map read) ∧
        (RankMinimalExpression pick X n w s →
          RankMinimalExpression pick X n (FreeGroup.mk (l.map read))⁻¹ t ∧
          ∀ j, rankCount s j = rankCount [y] j + rankCount t j) := by
  classical
  intro rows P z read hc hz
  obtain ⟨hfix,hcycle,hn⟩ := oneDart_leaf P z hz
  let S := P.edgeSplice z
  let e := P.edge z
  let idx := discOccurrence (markedRows rows w) (boundaryIdentity s)
  let v : _ → F := fun d => FreeGroup.mk [read d]
  have hES : S.EulerEquality :=
    (P.edgeSplice_euler_iff z hn).mpr (boundaryRibbon_euler rows w s hs)
  have hCS : S.Connected := guba22_edgeSplice_connected P hc z hn
  have hedge : ∀ d, read (P.edge d) = reverseLetter (read d) :=
    relatorRibbon_edge_read (chosenSection (Fin 2))
      (markedRows rows w) (boundaryIdentity s) (boundaryIdentity_evaluation rows w s hs)
  have he : ∀ d, v (S.edge d) = (v d)⁻¹ := by
    intro d
    change FreeGroup.mk [read (P.edge d)] = (FreeGroup.mk [read d])⁻¹
    rw [hedge]
    exact signedLetterValue_reverse _
  have hv (Q : RibbonMap _) (d : _) :
      cycleProduct Q.rotation v d = FreeGroup.mk ((Q.vertexBoundary d).map read) := by
    change ((Q.vertexBoundary d).map v).prod = _
    rw [rawWord_eval_prod,List.map_map]
    rfl
  have outside (d : _) (hd : ¬ S.rotation.SameCycle z d) :
      ¬ P.rotation.SameCycle z d ∧ ¬ P.rotation.SameCycle e d := by
    constructor
    · intro h
      exact hd ((P.edgeSplice_sameVertex_iff z hn z d).mpr (Or.inl h))
    · intro h
      exact hd ((P.edgeSplice_sameVertex_iff z hn z d).mpr
        (Or.inr ⟨Or.inl (.refl _ _),Or.inr h.symm⟩))
  have keep (d : _) (hd : ¬ S.rotation.SameCycle z d) :
      cycleProduct S.rotation v d = cycleProduct P.rotation v d := by
    apply guba23_splice_keep_vertex_product P v z d hn
    rw [hfix]
    exact hd
  have hidx (d : _) (hd : ¬ S.rotation.SameCycle z d) :
      idx d ≠ boundaryOccurrence s := by
    intro h
    exact (outside d hd).1 ((boundaryDart_sameVertex_iff rows w s hs hw d).mpr h)
  have heidx : idx e ≠ boundaryOccurrence s := by
    intro h
    exact hn ((boundaryDart_sameVertex_iff rows w s hs hw e).mpr h)
  obtain ⟨deletedIndex,y,homit,hylabel,hy⟩ := guba23_vertex_factor_as_occurrence rows w s hs e 1 heidx
  obtain ⟨f,hf,hsep,_,hprod⟩ :=
    guba23_component_exact_vertex_product S v he hCS hES z
  let value : F × _ → F := fun t => t.1 * cycleProduct S.rotation v t.2 * t.1⁻¹
  have build (b : List (F × _))
      (hb : ∀ t ∈ b, ¬ S.rotation.SameCycle z t.2)
      (hp : b.Pairwise (fun t u => ¬ S.rotation.SameCycle t.2 u.2)) :
      ∃ l : List (Fin s.length × Peiffer.Occurrence F (RankHeight n)),
        (l.map Prod.fst).Nodup ∧
        (∀ t ∈ l, t.2.1.2 = s[t.1.val].1.2 ∧
          ∃ u ∈ b, (idx u.2).val = t.1.val+1) ∧
        Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) (l.map Prod.snd) =
          (b.map value).prod := by
    induction b with
    | nil => exact ⟨[],by simp,by simp,rfl⟩
    | cons u us ih =>
      obtain ⟨i,y,hi,hy,hval⟩ := guba23_vertex_factor_as_occurrence
        rows w s hs u.2 u.1 (hidx u.2 (hb u List.mem_cons_self))
      obtain ⟨l,hl,hcover,hev⟩ := ih
        (fun t ht => hb t (List.mem_cons_of_mem _ ht)) (List.pairwise_cons.mp hp).2
      refine ⟨(i,y)::l,?_,?_,?_⟩
      · simp only [List.map_cons,List.nodup_cons]
        refine ⟨?_,hl⟩
        intro hmem
        obtain ⟨t,ht,hti⟩ := List.mem_map.mp hmem
        obtain ⟨_,q,hq,hqi⟩ := hcover t ht
        have hs' : P.rotation.SameCycle u.2 q.2 := by
          change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle u.2 q.2
          rw [disc_sameCycle_iff]
          apply Fin.ext
          rw [hi,hqi,hti]
        exact (List.pairwise_cons.mp hp).1 q hq
          ((P.edgeSplice_sameVertex_iff z hn u.2 q.2).mpr (Or.inl hs'))
      · intro t ht
        rcases List.mem_cons.mp ht with ht | ht
        · subst t
          exact ⟨hy,u,List.mem_cons_self,hi⟩
        · obtain ⟨hlabel,q,hq,hqi⟩ := hcover t ht
          exact ⟨hlabel,q,List.mem_cons_of_mem _ hq,hqi⟩
      · change Peiffer.term (fun i => FreeGroup.mk (rows i)) y *
          Peiffer.evaluation (fun i => FreeGroup.mk (rows i)) (l.map Prod.snd) =
          value u * (us.map value).prod
        rw [hev]
        have hval' : Peiffer.term (fun i => FreeGroup.mk (rows i)) y = value u := by
          change _ = u.1 * cycleProduct S.rotation v u.2 * u.1⁻¹
          rw [keep u.2 (hb u List.mem_cons_self),hv]
          exact hval
        rw [hval']
  obtain ⟨l,hl,hcover,hev⟩ := build f hf hsep
  have hnot : deletedIndex ∉ l.map Prod.fst := by
    intro hmem
    obtain ⟨t,ht,hti⟩ := List.mem_map.mp hmem
    obtain ⟨_,d,hd,hdi⟩ := hcover t ht
    have hsame : P.rotation.SameCycle e d.2 := by
      change (discRotation (markedRows rows w) (boundaryIdentity s)).SameCycle e d.2
      rw [disc_sameCycle_iff]
      apply Fin.ext
      rw [homit,hdi,hti]
    exact (outside d.2 (hf d hd)).2 hsame
  have hlt := rank_type_lt_of_omitted_index s (l.map Prod.snd)
    (l.map Prod.fst) hl (indexed_rankCount_eq s l (fun t ht => (hcover t ht).1)) deletedIndex hnot
  obtain ⟨tail,htail⟩ := cycleBoundary_cons P.rotation e
  change P.vertexBoundary e = e::tail at htail
  have hread : (S.vertexBoundary z).map read =
      [read z,read e] ++ tail.map read := by
    have h := edgeSplice_vertex_read P read z hn
    rw [hfix,hz,htail] at h
    exact h
  have hcancel : FreeGroup.mk [read z,read e] = 1 := by
    change FreeGroup.mk [read z,read (P.edge z)] = 1
    rw [hedge]
    change FreeGroup.mk ([read z] ++ [reverseLetter (read z)]) = 1
    rw [← FreeGroup.mul_mk,signedLetterValue_reverse,mul_inv_cancel]
  have hval : cycleProduct S.rotation v z = FreeGroup.mk (tail.map read) := by
    rw [hv,hread,← FreeGroup.mul_mk,hcancel,one_mul]
  have hp : FreeGroup.mk (tail.map read) * (f.map value).prod = 1 := by
    rw [← hval]
    exact hprod
  have heval : Peiffer.evaluation (rankHeightRel pick X n) (l.map Prod.snd) =
      (FreeGroup.mk (tail.map read))⁻¹ := by
    have hv' : (f.map value).prod = (FreeGroup.mk (tail.map read))⁻¹ := by
      calc
        _ = (FreeGroup.mk (tail.map read))⁻¹ *
          (FreeGroup.mk (tail.map read) * (f.map value).prod) := by group
        _ = _ := by rw [hp,mul_one]
    simpa only [rows,rankHeightRows_eval] using hev.trans hv'
  have hzval : FreeGroup.mk [read z] = w⁻¹ := by
    have h := boundaryRibbon_read rows w s hs hw
    change (P.vertexBoundary z).map read = FreeGroup.invRev w.toWord at h
    rw [hz] at h
    change [read z] = FreeGroup.invRev w.toWord at h
    rw [h,← FreeGroup.inv_mk,FreeGroup.mk_toWord]
  have hevalEdge : FreeGroup.mk [read e] = w := by
    have h := he z
    change FreeGroup.mk [read e] = (FreeGroup.mk [read z])⁻¹ at h
    rw [h,hzval,inv_inv]
  have hyval : Peiffer.term (rankHeightRel pick X n) y =
      w * FreeGroup.mk (tail.map read) := by
    change Peiffer.term (fun i => FreeGroup.mk (rows i)) y =
      (1 : F) * FreeGroup.mk ((P.vertexBoundary e).map read) * (1 : F)⁻¹ at hy
    simp only [one_mul,inv_one,mul_one,htail,List.map_cons] at hy
    change Peiffer.term (fun i => FreeGroup.mk (rows i)) y =
      FreeGroup.mk ([read e] ++ tail.map read) at hy
    rw [← FreeGroup.mul_mk,hevalEdge] at hy
    simpa only [rows,rankHeightRows_eval] using hy
  have hfull : Peiffer.evaluation (rankHeightRel pick X n)
      (y :: l.map Prod.snd) = w := by
    change Peiffer.term (rankHeightRel pick X n) y *
      Peiffer.evaluation (rankHeightRel pick X n) (l.map Prod.snd) = w
    rw [hyval,heval,mul_assoc,mul_inv_cancel,mul_one]
  refine ⟨tail,htail,deletedIndex,y,l.map Prod.snd,hylabel,heval,hfull,hlt,homit,hyval,?_⟩
  intro hm
  let L := (deletedIndex,y)::l
  have hnd : (L.map Prod.fst).Nodup := by
    change (deletedIndex :: l.map Prod.fst).Nodup
    exact List.nodup_cons.mpr ⟨hnot,hl⟩
  have hlabels (x : Fin s.length × Peiffer.Occurrence F (RankHeight n))
      (hx : x ∈ L) : x.2.1.2 = s[x.1.val].1.2 := by
    change x ∈ (deletedIndex,y)::l at hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact hylabel
    · exact (hcover x hx).1
  obtain ⟨hmin,hprofile⟩ :=
    rankMinimal_indexed_reassembly pick X n w s hm L hnd hlabels hfull
  have hm' : RankMinimalExpression pick X n w
      ([y] ++ l.map Prod.snd ++ []) := by
    simpa [L] using hmin
  have ht := rankMinimal_subfilling_minimal pick X n w [y] (l.map Prod.snd) [] hm'
  rw [heval] at ht
  refine ⟨ht,?_⟩
  intro j
  have h := hprofile j
  change rankCount s j = rankCount ([y] ++ l.map Prod.snd) j at h
  rw [rankCount_append] at h
  exact h

#print axioms oneDart_rankMinimal_defect_exact_type

/-- Boundary-value consequence, without assuming the parent is minimal. -/
theorem oneDart_rankMinimal_defect_smaller_type
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight n))
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X n i)) s = w)
    (hw : w ≠ 1) :
    let rows := rankHeightRows pick X n
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    P.Connected → P.vertexBoundary z = [z] →
    ∃ l : List _, P.vertexBoundary (P.edge z) = P.edge z::l ∧
      ∃ t : Peiffer.Sequence F (RankHeight n),
        RankMinimalExpression pick X n (FreeGroup.mk (l.map read))⁻¹ t ∧
        descendingCountLT n rankCount t s := by
  intro rows P z read hc hz
  obtain ⟨l,hl,_,_,t,_,he,_,hlt,_,_,_⟩ :=
    oneDart_rankMinimal_defect_exact_type pick X n w s hs hw hc hz
  exact ⟨l,hl,rankMinimal_exists_below_type pick X n _ s t he hlt⟩

#print axioms oneDart_rankMinimal_defect_smaller_type

#print axioms topRankFilling
#print axioms topHeightProduct
#print axioms initialWeightedPeriod
#print axioms affineFixedPolynomial
#print axioms affinePerm
#print axioms affineFreeMap
#print axioms twoPeriodSelector


/-- A filling with no occurrence of the top rank is already a
relation in the preceding stage. This holds with either orientation,
and is the converse to the existing lower-rank filling construction. -/
theorem top_count_zero_mem_lower
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ)
    (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hz : rankCount s j = 0) :
    Peiffer.evaluation (rankHeightRel pick X (j+1)) s ∈
      weightedHeightStage pick X j := by
  let N := weightedStages pick X j
  let : N.Normal := weightedStages_normal pick X j
  rw [weightedHeightStage_eq]
  change Peiffer.evaluation (rankHeightRel pick X (j+1)) s ∈ N
  induction s with
  | nil => exact N.one_mem
  | cons x xs ih =>
    have hcount : rankCount (x::xs) j = rankCount [x] j + rankCount xs j :=
      rankCount_append [x] xs j
    have h0 : rankCount [x] j = 0 := by omega
    have hx0 : x.1.2.1.val ≠ j := by
      intro h
      rw [rankCount_singleton,if_pos h] at h0
      omega
    have hlt : x.1.2.1.val < j := by
      have h := x.1.2.1.isLt
      omega
    have hr : rankHeightRel pick X (j+1) x.1.2 ∈ N := by
      change weightedRankHeightRelator pick X x.1.2.1.val x.1.2.2 ∈
        weightedStages pick X j
      rw [← weightedHeightStage_eq]
      exact Subgroup.subset_normalClosure ⟨_,hlt,_,rfl⟩
    have ht : Peiffer.term (rankHeightRel pick X (j+1)) x ∈ N := by
      rcases x with ⟨⟨u,i⟩,sg⟩
      cases sg
      · have h := (inferInstance : N.Normal).conj_mem _ hr u
        simpa only [Peiffer.term,Bool.cond_false] using N.inv_mem h
      · change u * rankHeightRel pick X (j+1) i * u⁻¹ ∈ N
        exact (inferInstance : N.Normal).conj_mem _ hr _
    change Peiffer.term (rankHeightRel pick X (j+1)) x *
      Peiffer.evaluation (rankHeightRel pick X (j+1)) xs ∈ N
    exact N.mul_mem ht (ih (by omega))

/-- For a rank-minimal expression, the top count vanishes exactly
when the boundary belongs to the preceding stage. -/
theorem rankMinimal_top_count_zero_iff
    (pick : WeightedSelector) (X : ConjugatorChoice) (j : ℕ)
    (w : F) (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s) :
    rankCount s j = 0 ↔ w ∈ weightedHeightStage pick X j := by
  constructor
  · intro h
    rw [← hm.1]
    exact top_count_zero_mem_lower pick X j s h
  · intro h
    have hmod : (Peiffer.evaluation (rankHeightRel pick X (j+1))
      ([] : Peiffer.Sequence F (RankHeight (j+1))))⁻¹ * w ∈
        weightedHeightStage pick X j := by
      simpa [Peiffer.evaluation] using h
    have hle := rankMinimal_top_count_of_modular_filling pick X j w s [] hm hmod
    change rankCount s j ≤ 0 at hle
    omega

/-- An exact deletion detects whether the literal defect is a
lower-rank relation, solely from the original top count and the
rank of the deleted occurrence. No assumption about the size of
the other cells is required. -/
theorem oneDart_defect_lower_iff_top_count
    (pick : WeightedSelector) (X : ConjugatorChoice)
    (j : ℕ) (w : F) (s : Peiffer.Sequence F (RankHeight (j+1)))
    (hm : RankMinimalExpression pick X (j+1) w s)
    (hs : Peiffer.evaluation
      (fun i => FreeGroup.mk (rankHeightRows pick X (j+1) i)) s = w)
    (hw : w ≠ 1) :
    let rows := rankHeightRows pick X (j+1)
    let P := boundaryRibbon rows w s hs
    let z := boundaryDart rows w s hw
    let read := discRead (chosenSection (Fin 2)) (markedRows rows w) (boundaryIdentity s)
    P.Connected → P.vertexBoundary z = [z] →
    ∃ (l : List _) (i : Fin s.length),
      P.vertexBoundary (P.edge z) = P.edge z::l ∧
      (discOccurrence (markedRows rows w) (boundaryIdentity s)
        (P.edge z)).val = i.val+1 ∧
      (FreeGroup.mk (l.map read) ∈ weightedHeightStage pick X j ↔
        rankCount s j = if s[i.val].1.2.1.val = j then 1 else 0) := by
  intro rows P z read hc hz
  obtain ⟨l,hl,i,y,t,hy,_,_,_,hidx,_,hmin⟩ :=
    oneDart_rankMinimal_defect_exact_type pick X (j+1) w s hs hw hc hz
  obtain ⟨ht,hprofile⟩ := hmin hm
  have hcount := hprofile j
  rw [rankCount_singleton,hy] at hcount
  refine ⟨l,i,hl,hidx,?_⟩
  have hinv : FreeGroup.mk (l.map read) ∈ weightedHeightStage pick X j ↔
      (FreeGroup.mk (l.map read))⁻¹ ∈ weightedHeightStage pick X j := by
    constructor
    · exact fun h => (weightedHeightStage pick X j).inv_mem h
    · intro h
      simpa only [inv_inv] using (weightedHeightStage pick X j).inv_mem h
  rw [hinv,← rankMinimal_top_count_zero_iff pick X j _ t ht]
  omega

/-- A unit-height relator with a base commuting with the light
generator in the preceding quotient cannot equal a power of that
generator. This includes shifts based by a pure light power. -/
theorem unit_height_light_aligned_impossible
    (N : Subgroup F) [N.Normal] (c u v : F) (k m : ℤ)
    (hc : MinBad N c) (hk : k = 1 ∨ k = -1) :
    let q := QuotientGroup.mk' N
    Commute (q v) (q a) →
    q (v * heightRelator u c k * v⁻¹) ≠ q (a^m) := by
  intro q hcomm he
  have hcomm' : Commute (q v) (q (a^m)) := by
    rw [map_zpow]
    exact hcomm.zpow_right m
  have hr : q (heightRelator u c k) = q (a^m) := by
    simp only [map_mul,map_inv] at he
    calc
      _ = (q v)⁻¹ * (q v * q (heightRelator u c k) * (q v)⁻¹) * q v := by group
      _ = _ := by rw [he,mul_assoc,← hcomm'.eq,← mul_assoc,inv_mul_cancel,one_mul]
  have heq : q u * (q c)^k * (q u)⁻¹ = (q a)^(m+k) := by
    simp only [heightRelator,map_mul,map_inv,map_zpow] at hr
    calc
      _ = (q u * (q c)^k * (q u)⁻¹ * ((q a)^k)⁻¹) * (q a)^k := by group
      _ = _ := by rw [hr,← zpow_add]
  have hg : Good N (c^k) := by
    apply (good_iff_quotient N (c^k)).mpr
    refine ⟨m+k,isConj_iff.mpr ⟨q u,?_⟩⟩
    rw [map_zpow]
    exact heq
  apply hc.1
  rcases hk with hk | hk
  · simpa only [hk,zpow_one] using hg
  · have hh := good_integer_power N hg (-1)
    simpa only [hk,zpow_neg_one,inv_inv] using hh

#print axioms top_count_zero_mem_lower
#print axioms rankMinimal_top_count_zero_iff
#print axioms oneDart_defect_lower_iff_top_count
#print axioms unit_height_light_aligned_impossible


/-- Direct terminal criterion for the one-letter survival approach.
A single corridor, with inner arc at least 10^-18 of the cell
perimeter and the local transfer inequality of Lemma 21, suffices.
The inner and outer words are supplied by the proposed geometric
certificate; no coverage or simultaneous disjointness is asserted.
All inequalities are integral, avoiding real-valued conversions. -/
theorem answer_of_guba_one_dart_single_arc
    (step : ∀ j (s : Peiffer.Sequence F (RankHeight (j+1)))
      (hs : Peiffer.evaluation
        (fun i => FreeGroup.mk (rankHeightRows twoPeriodSelector
          (gubaConjugatorChoice twoPeriodSelector) (j+1) i)) s = a),
      a ∉ weightedHeightStage twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) j →
      RankMinimalExpression twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) (j+1) a s →
      (∀ x ∈ s, x.2 = true) →
      let rows := rankHeightRows twoPeriodSelector
        (gubaConjugatorChoice twoPeriodSelector) (j+1)
      let P := boundaryRibbon rows a s hs
      let z := boundaryDart rows a s (show a ≠ 1 by
        intro h
        have hw : weightedLength a = 1 := by simpa using weightedLength_a_zpow 1
        rw [h] at hw
        have hz := (weightedLength_eq_zero_iff (1 : F)).mpr rfl
        omega)
      P.Connected → P.EulerEquality → P.vertexBoundary z = [z] →
      ∃ x ∈ s, ∃ inner outer : RawWord,
        outer.Sublist (FreeGroup.invRev a.toWord) ∧
        rawWeight (rows x.1.2) ≤ 10^18 * rawWeight inner ∧
        9 * 10^18 * rawWeight inner ≤
          10^19 * rawWeight outer + 2 * rawWeight (rows x.1.2)) :
    answer := by
  apply answer_of_guba_one_dart_step
  intro j s hs hnew hm hpos rows P z hc hE hz
  obtain ⟨x,hx,inner,outer,hsub,hL,hT⟩ :=
    step j s hs hnew hm hpos hc hE hz
  have hB := guba23_sublist_weight hsub
  rw [rawWeight_invRev] at hB
  change rawWeight outer ≤ weightedLength a at hB
  have ha : weightedLength a = 1 := by
    simpa using weightedLength_a_zpow 1
  rw [ha] at hB
  obtain ⟨p,r,he⟩ := List.mem_iff_append.mp hx
  have hn : rankHeightRows twoPeriodSelector
      (gubaConjugatorChoice twoPeriodSelector) (j+1) x.1.2 ≠ [] := by
    apply rankMinimal_designated_row_nonempty twoPeriodSelector
      (gubaConjugatorChoice twoPeriodSelector) (j+1) a p r x
    have hsplit : s = p ++ [x] ++ r := by simpa using he
    exact hsplit ▸ hm
  have hlarge := guba_rankHeightRows_large twoPeriodSelector (j+1) x.1.2 hn
  change rawWeight (rankHeightRows twoPeriodSelector
    (gubaConjugatorChoice twoPeriodSelector) (j+1) x.1.2) ≤
      10^18 * rawWeight inner at hL
  change 9 * 10^18 * rawWeight inner ≤
    10^19 * rawWeight outer + 2 * rawWeight (rankHeightRows twoPeriodSelector
      (gubaConjugatorChoice twoPeriodSelector) (j+1) x.1.2) at hT
  norm_num at hL hT hlarge
  omega

#print axioms answer_of_guba_one_dart_single_arc


/-- Minimal bad periods are invariant under reversal of orientation.
The proof uses only closure of goodness under integer powers. -/
theorem minBad_inverse {N : Subgroup F} [N.Normal] {c : F}
    (hc : MinBad N c) : MinBad N c⁻¹ := by
  constructor
  · intro hg
    apply hc.1
    simpa only [zpow_neg_one,inv_inv] using good_integer_power N hg (-1)
  · intro w hw
    have he : weightedLength c⁻¹ = weightedLength c := by
      simp only [weightedLength,FreeGroup.toWord_inv,rawWeight_invRev]
    rw [he]
    exact hc.2 w hw

/-- For a corridor with no interior relations, a freely reduced
inner reading satisfies the local transfer bound with coefficient
one, rather than rho=.9. Both actual side words are charged.
There is no small-cancellation or smoothness hypothesis here. -/
theorem rankZero_quadrilateral_inner_weight
    (inner outer left right : RawWord)
    (hred : FreeGroup.IsReduced inner)
    (hboundary : FreeGroup.mk ((inner ++ right) ++ FreeGroup.invRev (left ++ outer)) = 1) :
    rawWeight inner ≤ rawWeight outer + rawWeight left + rawWeight right := by
  have he : FreeGroup.mk inner = FreeGroup.mk (left ++ outer ++ FreeGroup.invRev right) := by
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk] at hboundary ⊢
    calc
      _ = (FreeGroup.mk inner * FreeGroup.mk right *
        (FreeGroup.mk left * FreeGroup.mk outer)⁻¹) *
        (FreeGroup.mk left * FreeGroup.mk outer * (FreeGroup.mk right)⁻¹) := by group
      _ = _ := by rw [hboundary,one_mul]
  have hi : weightedLength (FreeGroup.mk inner) = rawWeight inner := by
    rw [weightedLength,FreeGroup.toWord_mk,hred.reduce_eq]
  have h := weightedLength_mk_le (left ++ outer ++ FreeGroup.invRev right)
  rw [← he,hi,rawWeight_append,rawWeight_append,rawWeight_invRev] at h
  omega

/-- Local transfer on a signed cyclic factor of at most one period.
The lower quotient is the one in which the period is minimal bad.
Thus this case of the terminal corridor argument needs neither
Lemma 21 nor the smaller-type perimeter estimate of Lemma 23. -/
theorem minBad_signed_cyclicFactor_quadrilateral_weight
    {N : Subgroup F} [N.Normal] {c : F} (hc : MinBad N c)
    (sg : Bool) (l r p inner q outer left right : RawWord)
    (hword : (if sg then c else c⁻¹).toWord = l ++ r)
    (hfactor : r ++ l = p ++ inner ++ q)
    (hboundary : FreeGroup.mk ((inner ++ right) ++
      FreeGroup.invRev (left ++ outer)) ∈ N) :
    rawWeight inner ≤ rawWeight outer + rawWeight left + rawWeight right := by
  have hmin : MinBad N (if sg then c else c⁻¹) := by
    cases sg
    · simpa using minBad_inverse hc
    · simpa using hc
  exact minBad_cyclicFactor_quadrilateral_weight hmin l r p inner q outer left right
    hword hfactor hboundary

/-- Convert the stronger coefficient-one transfer to the exact
integer inequality used in answer_of_guba_one_dart_single_arc.
The side budget is the sum, not a bound on just one side. -/
theorem oneDart_local_transfer_of_short_sides
    (P : ℕ) (inner outer left right : RawWord)
    (hlocal : rawWeight inner ≤ rawWeight outer + rawWeight left + rawWeight right)
    (hsides : 10^19 * (rawWeight left + rawWeight right) ≤ 2 * P) :
    9 * 10^18 * rawWeight inner ≤ 10^19 * rawWeight outer + 2 * P := by
  norm_num at hsides ⊢
  omega

#print axioms minBad_inverse
#print axioms rankZero_quadrilateral_inner_weight
#print axioms minBad_signed_cyclicFactor_quadrilateral_weight
#print axioms oneDart_local_transfer_of_short_sides

end QuandleResearch.Issue070
