import QuandleResearch.Questions.Issue014

/-! Comparator-only specification, deliberately isolated from the proof.
The two private assumptions provide expected theorem signatures to Lake's
challenge exporter. They are not allowed axioms of the submitted solution.
Never import this module into the proof or the proof audit. The comparator
checks the exact declarations and all referenced definitions against the
solution, then checks the solution's axioms and exported proof terms. -/

namespace QuandleResearch.Q525

private axiom expectedB : Issue014.negativeB.{0}

theorem partB : Issue014.negativeB.{0} := expectedB

namespace MatrixModel

private axiom expectedA : Issue014.negativeA.{0}

theorem partA : Issue014.negativeA.{0} := expectedA

theorem solution : Issue014.bothNegative.{0} :=
  ⟨partA, QuandleResearch.Q525.partB⟩

end MatrixModel
end QuandleResearch.Q525
