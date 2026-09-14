import Tarski.Eval
import Tarski.Format

/-! The `Error` refinements: `cause`, `AggregateError`, `Error.isError`,
and the absence of `stack`.

`cause` lands in the one arm the seven constructors share, so it is one
InstallErrorCause for all of them; it is non-enumerable and defined after
`message`, which is what `Object.getOwnPropertyNames` reads back.

`AggregateError` is a native of its own rather than an eighth
`ErrorKind`: `ErrorKind` is the set the evaluator itself throws and the
set the emitter accepts by name, and its order fixes the realm's first
references and cells. Its `errors` is read as an **array-like** rather
than iterated — IterableToList is #394's — which is the one place this
differs from the specification, and it differs only for an argument that
has a `length` and no `@@iterator`.

`stack` is absent **by design**, not by omission: it is not in the
specification, and an evaluator with no call stack to report has nothing
honest to put there. The two guards at the end pin the absence. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- A program that is one expression. -/
private def expr (e : Expr) : Program := [.exprStmt e]

/-- `new <name>(<args>)`. -/
private def make (name : String) (args : List Expr) : Expr := .new (.ident name) args

/-- `{ cause: <e> }`. -/
private def causeOpts (e : Expr) : Expr := .objectLit [.init "cause" (e)]

/-! ## `cause` -/

#guard outcome (expr (.member (make "TypeError" [.strLit "m", causeOpts (.numLit 1.0)])
  "cause")) == "1"
#guard outcome (expr (.member (make "TypeError" [.strLit "m", causeOpts (.numLit 1.0)])
  "message")) == "m"

-- A `cause` of `undefined` is still an own property: the check is
-- HasProperty, not a comparison against `undefined`.
#guard outcome (expr (.call (.member (make "Error" [.strLit "m", causeOpts .undefLit])
  "hasOwnProperty") [.strLit "cause"])) == "true"
#guard outcome (expr (.call (.member (make "Error" [.strLit "m", .objectLit []])
  "hasOwnProperty") [.strLit "cause"])) == "false"
#guard outcome (expr (.call (.member (make "Error" [.strLit "m"]) "hasOwnProperty")
  [.strLit "cause"])) == "false"
-- A primitive `options` has no `cause` to install.
#guard outcome (expr (.call (.member (make "Error" [.strLit "m", .numLit 0.0])
  "hasOwnProperty") [.strLit "cause"])) == "false"
-- An inherited `cause` counts, HasProperty walking the chain.
#guard outcome
  [ .varDecl .«const» [{ target := "p", init := some (.objectLit [.init "cause" (.numLit 5.0)]) }],
    .exprStmt (.member (make "Error"
      [.strLit "m", .call (.member (.ident "Object") "create") [.ident "p"]]) "cause") ] == "5"

-- Non-enumerable, and after `message`.
#guard outcome (expr (.call (.member (make "Error" [.strLit "m", causeOpts (.numLit 1.0)])
  "propertyIsEnumerable") [.strLit "cause"])) == "false"
#guard outcome (expr (.call (.member (.call (.member (.ident "Object") "getOwnPropertyNames")
  [make "Error" [.strLit "m", causeOpts (.numLit 1.0)]]) "join") [.strLit ","]))
  == "message,cause"

-- A message-less constructor still installs the cause.
#guard outcome (expr (.member (make "Error" [.undefLit, causeOpts (.numLit 1.0)])
  "cause")) == "1"
#guard outcome (expr (.call (.member (make "Error" [.undefLit, causeOpts (.numLit 1.0)])
  "hasOwnProperty") [.strLit "message"])) == "false"

-- All seven kinds share the one arm.
#guard ErrorKind.all.all fun k =>
  outcome (expr (.member (make k.name [.strLit "m", causeOpts (.numLit 1.0)]) "cause")) == "1"

/-! ## `AggregateError` -/

/-- `new AggregateError([e1, e2], "m", { cause: 0 })`. -/
private def agg : Expr :=
  make "AggregateError"
    [ .arrayLit [.strLit "e1", .strLit "e2"], .strLit "m", causeOpts (.numLit 0.0) ]

#guard outcome (expr (.member (.member agg "errors") "length")) == "2"
#guard outcome (expr (.index (.member agg "errors") (.numLit 0.0))) == "e1"
#guard outcome (expr (.member agg "message")) == "m"
#guard outcome (expr (.member agg "cause")) == "0"
#guard outcome (expr (.member agg "name")) == "AggregateError"
#guard outcome (expr (.binary .instanceof agg (.ident "Error"))) == "true"
#guard outcome (expr (.binary .instanceof agg (.ident "AggregateError"))) == "true"
#guard outcome (expr (.call (.member agg "toString") [])) == "AggregateError: m"

-- `errors` is a fresh array, and it is non-enumerable.
#guard outcome
  [ .varDecl .«const» [{ target := "xs", init := some (.arrayLit [.numLit 1.0]) }],
    .exprStmt (.binary .strictEq
      (.member (make "AggregateError" [.ident "xs"]) "errors") (.ident "xs")) ] == "false"
#guard outcome (expr (.call (.member agg "propertyIsEnumerable") [.strLit "errors"])) == "false"

-- The realm's two links, and 17.1's shape.
#guard outcome (expr (.binary .strictEq
  (.member (.member (.ident "AggregateError") "prototype") "constructor")
  (.ident "AggregateError"))) == "true"
#guard outcome (expr (.member (.ident "AggregateError") "length")) == "2"
#guard outcome (expr (.binary .strictEq
  (.call (.member (.ident "Object") "getPrototypeOf") [.ident "AggregateError"])
  (.ident "Error"))) == "true"

-- Called without `new`, it constructs, as the seven do.
#guard outcome (expr (.member (.member
  (.call (.ident "AggregateError") [.arrayLit []]) "errors") "length")) == "0"

-- Step 4 is IterableToList, so a string argument is `is not iterable`
-- until `String.prototype` has an `@@iterator` (#391).
#guard outcome (expr (.member (.member (make "AggregateError" [.strLit "ab"]) "errors")
  "length")) == "uncaught: TypeError: ab is not iterable"

-- `undefined` is not iterable.
#guard outcome (expr (make "AggregateError" []))
  == "uncaught: TypeError: undefined is not iterable"
#guard outcome (expr (make "AggregateError" [.nullLit]))
  == "uncaught: TypeError: null is not iterable"

/-! ## `Error.isError` -/

#guard outcome (expr (.call (.member (.ident "Error") "isError") [make "TypeError" []]))
  == "true"
#guard outcome (expr (.call (.member (.ident "Error") "isError") [agg])) == "true"
#guard outcome (expr (.call (.member (.ident "Error") "isError") [.objectLit []])) == "false"
#guard outcome (expr (.call (.member (.ident "Error") "isError") [.numLit 1.0])) == "false"
-- `Error.prototype` is an ordinary object: `[[ErrorData]]` is on the
-- instances.
#guard outcome (expr (.call (.member (.ident "Error") "isError")
  [.member (.ident "Error") "prototype"])) == "false"

/-! ## `stack` is absent by design -/

#guard outcome (expr (.binary .«in» (.strLit "stack") (make "Error" []))) == "false"
#guard outcome (expr (.call (.member (.member (.ident "Error") "prototype") "hasOwnProperty")
  [.strLit "stack"])) == "false"
