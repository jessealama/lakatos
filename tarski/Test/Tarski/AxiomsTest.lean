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
#eval onlyStandard ``Tarski.evalExprs

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalProps

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalDeclarators

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalWhile

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.callFunction

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.construct

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getProp

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.setProp

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.toPrimitive

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.primitiveFrom

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.toPropertyKey

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.instantiateBlock

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.makeFunction

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalProgram

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.runProgram

-- Catching a completion is an opaque definition with a monotonicity
-- lemma of its own, because `partial_fixpoint` has none for `tryCatch`.
-- Both rest on nothing beyond the standard three.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.catchReturn

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.monotone_catchReturn

-- The unfolding equations the proofs rewrite with are theorems of the
-- same standing: if they were not, every postcondition proved through a
-- `while` or a prototype walk would rest on whatever they did assume.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalWhile.eq_def

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getProp.eq_def
