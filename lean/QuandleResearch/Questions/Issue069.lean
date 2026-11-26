import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.LinkPresentations

/-!
# Issue 69: Darné Remark 7.31 (2026 v3) — completeness of the reduced fundamental quandle
https://github.com/555tery/quandle-orbit-series/issues/69

Formalization status: PARTIAL.
Remaining obligation: Universal reduced quotient and fundamental quandle presentation specified. Welded link-homotopy and reversed mirror of non-split components in S4 still need geometric encoding.

Source and target from the issue:
## Source / explicitly formulated conjecture
Jacques Darné, *Nilpotent quandles*, [arXiv:2205.02480v3, p. 43, Remark 7.31](https://arxiv.org/pdf/2205.02480v3#page=43). Source text and PDF page image checked.

## Target
Prove or disprove the conjecture that the reduced fundamental quandle is a complete invariant of welded links modulo welded link-homotopy and reversed mirror images of non-split components in the 4-dimensional sphere. Preserve the equivalence operations and dimensional qualification in the original statement.

## Source context / research leads
Definition 7.26 defines the reduced fundamental quandle as R(Q_L). Corollary 7.29 identifies it with the weak reduced peripheral system. Remark 7.31 contrasts this with the strong reduced peripheral system, with preferred longitudes, whose completeness is cited as [AM24]. The key issue is whether the lost information is precisely accounted for by the stated equivalence. The author also suggests enhancing the reduced quandle, possibly via cohomology, to recover the strong invariant; treat that as a related research direction, not an established equivalence.
Distinct from #56 (fundamental virtual knot biquandle) and #17 (cocycle invariants and link-homotopy).
-/

namespace QuandleResearch.Issue069
noncomputable section

def question {Link : Type} (reducedFundamental : Link → Quandle)
    (weldedHomotopyAndReversedMirrorsInS4 : Link → Link → Prop) : Prop :=
  ∀ l m, (reducedFundamental l).Iso (reducedFundamental m) ↔ weldedHomotopyAndReversedMirrorsInS4 l m

/-- Definition 7.26: the fundamental quandle followed by its universal
reduced quotient. The exact S4 equivalence is still external. -/
def completeReducedPresented {n : Nat} {Link : Type}
    (diagram : Link → ArcPresentation n)
    (weldedHomotopyAndReversedMirrorsInS4 : Link → Link → Prop) : Prop :=
  ∀ (l m : Link) (Q R U V : Quandle)
    (ql : (diagram l).Arc → Q.carrier) (qm : (diagram m).Arc → R.carrier)
    (p : Q.HomType U) (q : R.HomType V),
    (diagram l).PresentsQuandle Q ql → (diagram m).PresentsQuandle R qm →
    Q.IsReducedQuotient U p → R.IsReducedQuotient V q →
      (U.Iso V ↔ weldedHomotopyAndReversedMirrorsInS4 l m)

end
end QuandleResearch.Issue069
