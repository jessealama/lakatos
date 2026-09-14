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
#eval onlyStandard ``Tarski.evalBlock

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalCatch

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalLabeled

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalLoop

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.callFunction

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.construct

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.callNative

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.allocFromConstructor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.instanceOf

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.protoChainHas

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
#eval onlyStandard ``Tarski.toStringValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.setArrayLength

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.pushElements

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.joinElements

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
#eval onlyStandard ``Tarski.runScript

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.runProgram

-- The object operations #380 added: the array shape, the two
-- conversions at the arithmetic boundary, and the two allocators.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.newObject

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.newArray

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.newArrayOfLength

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.sameValueValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.uint32Of?

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Value.ofNat

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.arrayIndex?

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.digitsToNat

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.array

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.ownKeys

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.truncate

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.hasOwn

-- The realm is a literal, and the report that reads it is a definition
-- like any other.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Heap.initial

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.thrownSummary

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.describeThrown

-- The host's output log is heap data the binary reads back out.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Heap.printedLines

-- Catching a completion is an opaque definition with a monotonicity
-- lemma of its own, because `partial_fixpoint` has none for `tryCatch`.
-- There are two, and all four rest on nothing beyond the standard three.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.catchReturn

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.monotone_catchReturn

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.attempt

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.monotone_attempt

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.throwJsError

-- #382's dispatch: the coercions the built-ins go through, the shared
-- body of the unary `Math` members, the two `thisXValue` projections,
-- the radix check, and what `new` does to a wrapper native.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.toNumberValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.toNumberValues

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.mathUnary

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.thisNumberValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.thisBooleanValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.numberArg

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.constructNative

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.radix?

-- And the library definitions the `Math` members and `**` delegate to:
-- `tsPow` is built from `Float.Model`, never from an `extern`, which is
-- what makes the kernel able to reduce it.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.tsPow

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.powNat

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.powNatAux

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.natOfIntegral

-- The unfolding equations the proofs rewrite with are theorems of the
-- same standing: if they were not, every postcondition proved through a
-- `while` or a prototype walk would rest on whatever they did assume.
-- `protoChainHas` joins the two for the same reason: it recurses on the
-- heap, so it is `rw`'s and never a simp set's.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalWhile.eq_def

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getProp.eq_def

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.protoChainHas.eq_def

-- `joinElements` is the third: it recurses on an array's length.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.joinElements.eq_def
