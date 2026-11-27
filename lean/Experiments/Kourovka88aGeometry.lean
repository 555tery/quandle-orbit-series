module

public import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy
public import SmallPresentation.SmallCancellationDipoleIdentityRibbon
public import SmallPresentation.SmallCancellationGeometryIdentityPlanarity

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

@[expose] public section

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

end QuandleResearch.Issue070
