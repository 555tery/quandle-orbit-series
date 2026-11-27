module

public import QuandleResearch.Proofs.Kourovka88a.WeightedGreedy
public import SmallPresentation.SmallCancellationDipoleIdentityRibbon

/-!
# Experimental bridge to the pinned Small-Groups geometry library

This file is built by the isolated geometry workflow, not by the default
QuandleResearch target. The external library supplies actual finite row
ribbons, with literal occurrence indices and inverse-labelled edge pairing.
No small-cancellation, planarity, or rank-survival conclusion is assumed here.

The first bridge is independent of the spellings chosen for the relators.
The specialization below uses reduced spellings only as an integration
test; Guba's later diagram estimates must use audited literal height rows.
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
This is a realization of the marked identity, not yet a connected planar
reduced diagram or a geometric survival theorem. -/
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

/-- First integration test: use the canonical reduced spellings in the
existing algebraic stage. This does not assert they are the literal
cyclic height rows of Guba's original diagram system. -/
noncomputable def rankHeightRows (pick : WeightedSelector) (X : ConjugatorChoice)
    (n : ℕ) (i : RankHeight n) : RawWord :=
  (rankHeightRel pick X n i).toWord

theorem rankHeightRows_eval (pick : WeightedSelector)
    (X : ConjugatorChoice) (n : ℕ) (i : RankHeight n) :
    FreeGroup.mk (rankHeightRows pick X n i) = rankHeightRel pick X n i :=
  FreeGroup.mk_toWord _

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

end QuandleResearch.Issue070
