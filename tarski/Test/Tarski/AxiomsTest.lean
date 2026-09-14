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
#eval onlyStandard ``Tarski.evalDoWhile

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalDoLoop

-- FunctionDeclarationInstantiation and its four helpers: a call's scope
-- is built out of definitions like everything else.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.instantiateFunction

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.initParams

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.allocParams

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.hoistVarsFrom

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.makeArguments

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.mentionsArguments

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.expectedArgumentCount

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

-- #383's statements and operators: the `for` loop and its head, the
-- `switch`, the `var` pass every script now runs, and the pure helpers
-- the three of them share.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalForLoop

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalFor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalSwitch

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalCases

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.selectCase

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.runCases

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.dropUntilDefault

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.varNames

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.varNamesStmt

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.varNamesCases

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.hoistVars

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.copyBindings

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Env.rebind

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.putIdent

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.applyCoercing

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.UpdateOp.step

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

-- The accessor split and everything a class is made of.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getFrom

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.findAccessor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getFromUp

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.findAccessorUp

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.isConstructor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalClass

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.defineMethods

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.initializeInstance

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.initFields

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.initFieldList

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.constructClass

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.runConstructor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalSuperCall

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.superBase

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.superRead

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.privateName

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.readPrivate

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.writePrivate

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.addPrivate

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.bindPrivateNames

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.defineData

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.Obj.defineAccessor

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.ClassDef.privateNames

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

-- `evalFor` is the fourth, `evalWhile`'s twin.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalFor.eq_def

-- `evalDoWhile` is the fifth, `evalWhile`'s other twin: the body ahead
-- of the test, so its equation is a different one.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.evalDoWhile.eq_def

-- The library definitions the evaluator now dispatches to: the formatter,
-- the parser, and the two integer conversions. They are ordinary
-- definitions over `Float.Model`, so none of them reaches an `extern`,
-- and `Number::toString` in particular is not core's opaque
-- `Float.toString`.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.toIntegerOrInfinityValue

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.toDecimalString

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.toRadixString

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.toFixedString

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.toExponentialString

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.toPrecisionString

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.stringToNumber

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.parseFloat

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.parseInt

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.Decimal.shortest

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.Decimal.ofScientific

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.tsToInt32

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Js.Number.FloatOps.integerOrInfinity?

-- And the two prototype steps, which took `getProp`'s place on the
-- rw-only list when the walk was split from the dispatch.
/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.getFromUp.eq_def

/-- info: true -/
#guard_msgs in
#eval onlyStandard ``Tarski.findAccessorUp.eq_def
