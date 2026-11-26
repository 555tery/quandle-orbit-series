import QuandleResearch.Proofs.Q525.MatrixWitnesses

/-! Regression check for Question 5.25. These checks are executable
Lean commands, not comments asserting that the proofs succeeded.
The two questions must be negated independently, and the final
proof must use only the usual Lean axioms. -/

example : QuandleResearch.Issue014.negativeA.{0} :=
  QuandleResearch.Q525.MatrixModel.partA

example : QuandleResearch.Issue014.negativeB.{0} :=
  QuandleResearch.Q525.partB

example : QuandleResearch.Issue014.bothNegative.{0} :=
  QuandleResearch.Q525.MatrixModel.solution

/--
info: 'QuandleResearch.Q525.MatrixModel.partA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuandleResearch.Q525.MatrixModel.partA

/--
info: 'QuandleResearch.Q525.partB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuandleResearch.Q525.partB

/--
info: 'QuandleResearch.Q525.MatrixModel.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuandleResearch.Q525.MatrixModel.solution
