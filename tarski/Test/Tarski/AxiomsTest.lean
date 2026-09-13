import Lean
import Tarski.Eval

/-! The evaluator is a definition, not an assumption.

`partial_fixpoint` builds the recursion out of a chain-complete order
rather than out of `partial`'s opaque constant, so every equation the
proofs use is a theorem and the whole evaluator rests on nothing beyond
the three axioms Lean's own library does. A regression here — a `sorry`,
a `partial` slipped into the mutual block, an `extern` primitive — shows
up as a fourth name. -/

open Lean

private def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def onlyStandard (n : Name) : CoreM Bool := do
  let axioms ← collectAxioms n
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalExpr

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalStmt

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalStmts

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalDeclarators

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalWhile

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalProgram

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.runProgram

-- The unfolding equation the loop proofs rewrite with is a theorem of the
-- same standing: if it were not, every postcondition proved through a
-- `while` would rest on whatever it did assume.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalWhile.eq_def
