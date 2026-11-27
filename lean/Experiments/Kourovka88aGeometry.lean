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

end QuandleResearch.Issue070
