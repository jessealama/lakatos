import Tarski.Eval
import Tarski.Format

/-! The `Math` intrinsic.

Every member here *is* one of the library's definitions — `Math.abs` is
`Js.Number.FloatOps.tsAbs`, `Math.round` is `tsRound`, `Math.pow` is
`tsPow` — so what these cases pin is the dispatch around them: argument
coercion through ToNumber, arity, the signed zeros surviving the trip out
through `Object.is`, and `Math.max`/`min` coercing every argument before
folding the library's binary operations from the identities its header
names.

What is *not* here is pinned too. `Math` has no `[[Call]]` and no
`[[Construct]]`, and the transcendental members, `random`, `clz32`, and
`imul` are absent rather than faked — a missing member reads `undefined`,
which is an honest answer, where a wrong one would not be. `Math.pow` of a
non-integral exponent is the library's placeholder (#434), and it is
pinned as such. -/

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

/-- `-0`. -/
private def negZero : Expr := .unary .neg (.numLit 0.0)

/-- `Math.<name>(<args>);` -/
private def math (name : String) (args : List Expr) : Expr :=
  .call (.member (.ident "Math") name) args

/-- `Object.is(<a>, <b>);`, the only way to see a signed zero. -/
private def objectIs (a b : Expr) : Expr := .call (.member (.ident "Object") "is") [a, b]

/-- An object whose `valueOf` answers `<e>`, so ToPrimitive runs user
code. -/
private def valueOfObj (e : Expr) : Expr :=
  .objectLit [.init "valueOf" (.funcExpr none [] [.returnStmt (some e)])]

/-! ## `Math.abs` and `Math.sqrt`, the two core operations behind aliases -/

-- `Math.abs(-3.5);`
#guard outcome (expr (math "abs" [.unary .neg (.numLit 3.5)])) == "3.5"

-- `Object.is(Math.abs(-0), 0);` — abs clears the sign bit.
#guard outcome (expr (objectIs (math "abs" [negZero]) (.numLit 0.0))) == "true"

-- `Math.abs();` — a missing argument is `undefined`, hence NaN.
#guard outcome (expr (math "abs" [])) == "NaN"

-- `Math.abs(true);` — ToNumber of a boolean.
#guard outcome (expr (math "abs" [.boolLit true])) == "1"

-- `Math.abs({ valueOf: function () { return -2; } });` — ToPrimitive runs
-- user code, and the built-in is where it is called from.
#guard outcome (expr (math "abs" [valueOfObj (.unary .neg (.numLit 2.0))])) == "2"

-- `Math.sqrt(4);`
#guard outcome (expr (math "sqrt" [.numLit 4.0])) == "2"

-- `Math.sqrt(-1);`
#guard outcome (expr (math "sqrt" [.unary .neg (.numLit 1.0)])) == "NaN"

-- `Math.sqrt(2) === 1.4142135623730951;` — the comparison is in the
-- language, because the placeholder formatter would print `1.414214`.
#guard outcome
    (expr (.binary .strictEq (math "sqrt" [.numLit 2.0]) (.numLit 1.4142135623730951)))
  == "true"

/-! ## The roundings, and the signed zero each of them can produce -/

-- `Math.trunc(-2.5);`, `Math.floor(-2.5);`, `Math.ceil(-2.5);`
#guard outcome (expr (math "trunc" [.unary .neg (.numLit 2.5)])) == "-2"
#guard outcome (expr (math "floor" [.unary .neg (.numLit 2.5)])) == "-3"
#guard outcome (expr (math "ceil" [.unary .neg (.numLit 2.5)])) == "-2"

-- `Object.is(Math.ceil(-0.5), -0);`
#guard outcome (expr (objectIs (math "ceil" [.unary .neg (.numLit 0.5)]) negZero)) == "true"

-- `Math.round(2.5);` and `Math.round(-2.5);` — ties go toward `+∞`, so
-- the two are not mirror images.
#guard outcome (expr (math "round" [.numLit 2.5])) == "3"
#guard outcome (expr (math "round" [.unary .neg (.numLit 2.5)])) == "-2"

-- `Object.is(Math.round(-0.4), -0);` — the issue's own acceptance row.
#guard outcome (expr (objectIs (math "round" [.unary .neg (.numLit 0.4)]) negZero)) == "true"

-- `Math.sign(-3);`, `Object.is(Math.sign(-0), -0);`, `Math.sign(NaN);`
#guard outcome (expr (math "sign" [.unary .neg (.numLit 3.0)])) == "-1"
#guard outcome (expr (objectIs (math "sign" [negZero]) negZero)) == "true"
#guard outcome (expr (math "sign" [.ident "NaN"])) == "NaN"

/-! ## `Math.fround`, the binary32 narrowing -/

-- `Math.fround(0.1) === 0.10000000149011612;` — the issue's own
-- acceptance row.
#guard outcome
    (expr (.binary .strictEq (math "fround" [.numLit 0.1]) (.numLit 0.10000000149011612)))
  == "true"

-- `Math.fround(1.5);` — exactly representable at binary32, so unchanged.
#guard outcome (expr (math "fround" [.numLit 1.5])) == "1.5"

/-! ## `Math.max` and `Math.min`

The library's `tsMax`/`tsMin` are binary; the built-in coerces every
argument and folds them from the identities `FloatOps.lean` names. That is
what makes the empty call an infinity, a NaN anywhere propagate, and the
two zeros still ordered. -/

#guard outcome (expr (math "max" [])) == "-Infinity"
#guard outcome (expr (math "min" [])) == "Infinity"
#guard outcome (expr (math "max" [.numLit 1.0, .numLit 3.0, .numLit 2.0])) == "3"
#guard outcome (expr (math "min" [.numLit 1.0, .numLit 3.0, .numLit 2.0])) == "1"

-- A NaN operand wins from either side, which C `fmax` does not do.
#guard outcome (expr (math "max" [.ident "NaN", .numLit 1.0])) == "NaN"
#guard outcome (expr (math "max" [.numLit 1.0, .ident "NaN"])) == "NaN"

-- `Math.max(NaN, 1) !== Math.max(NaN, 1);` — the issue's own acceptance
-- row: the result really is NaN, not merely printed as one.
#guard outcome
    (expr (.binary .strictNe (math "max" [.ident "NaN", .numLit 1.0])
      (math "max" [.ident "NaN", .numLit 1.0])))
  == "true"

-- `Object.is(Math.max(-0, 0), 0);` and `Object.is(Math.min(0, -0), -0);`
#guard outcome (expr (objectIs (math "max" [negZero, .numLit 0.0]) (.numLit 0.0))) == "true"
#guard outcome (expr (objectIs (math "min" [.numLit 0.0, negZero]) negZero)) == "true"

-- `Math.max(true, 2);` — every argument is coerced.
#guard outcome (expr (math "max" [.boolLit true, .numLit 2.0])) == "2"

/-! `let log = ""; const a = { valueOf: … NaN }, b = { valueOf: … 1 };
Math.max(a, b); log;` — every argument is coerced, in order, *before* any
is compared, so `b`'s `valueOf` runs even though `a`'s already answered
NaN. A fold that coerced lazily would print `a`. -/
#guard outcome
    [ .varDecl .«let» [{ name := "log", init := some (.strLit "") }],
      .varDecl .«const»
        [ { name := "a",
            init := some (.objectLit
              [ .init "valueOf"
                 (.funcExpr none []
                   [ .exprStmt (.assign (.ident "log")
                       (.binary .add (.ident "log") (.strLit "a"))),
                     .returnStmt (some (.ident "NaN")) ])]) },
          { name := "b",
            init := some (.objectLit
              [ .init "valueOf"
                 (.funcExpr none []
                   [ .exprStmt (.assign (.ident "log")
                       (.binary .add (.ident "log") (.strLit "b"))),
                     .returnStmt (some (.numLit 1.0)) ])]) } ],
      .exprStmt (math "max" [.ident "a", .ident "b"]),
      .exprStmt (.ident "log") ]
  == "ab"

/-! ## `Math.pow`, which is `**`'s definition too -/

#guard outcome (expr (math "pow" [.numLit 2.0, .numLit 10.0])) == "1024"
#guard outcome (expr (math "pow" [.numLit 2.0, .unary .neg (.numLit 2.0)])) == "0.25"
#guard outcome (expr (math "pow" [.ident "NaN", .numLit 0.0])) == "1"
#guard outcome (expr (math "pow" [.numLit 1.0, .ident "Infinity"])) == "NaN"

-- `Math.pow(-8, 1 / 3);` — a negative base under a fractional exponent is
-- NaN by the specification, so this row is real.
#guard outcome
    (expr (math "pow" [.unary .neg (.numLit 8.0), .binary .div (.numLit 1.0) (.numLit 3.0)]))
  == "NaN"

-- `Math.pow(4, 0.5);` — **the placeholder, not the truth**: JavaScript
-- answers 2. The library has no transcendental model (#434), and
-- `Test/Js/FloatPowTest.lean` says so at the source.
#guard outcome (expr (math "pow" [.numLit 4.0, .numLit 0.5])) == "NaN"

-- `2 ** 53 === Math.pow(2, 53);` — one definition, two spellings.
#guard outcome
    (expr (.binary .strictEq (.binary .exponent (.numLit 2.0) (.numLit 53.0))
      (math "pow" [.numLit 2.0, .numLit 53.0])))
  == "true"

/-! ## The constants, each the library's own definition -/

#guard outcome (expr (.binary .strictEq (.member (.ident "Math") "PI")
  (.numLit 3.141592653589793))) == "true"
#guard outcome (expr (.binary .strictEq (.member (.ident "Math") "E")
  (.numLit 2.718281828459045))) == "true"
#guard outcome (expr (.binary .strictEq (.member (.ident "Math") "LN2")
  (.numLit 0.6931471805599453))) == "true"

/-! ## What `Math` is, and what it is not

`Math` is an ordinary object with neither `[[Call]]` nor `[[Construct]]`.
The members below are absent rather than faked: `cbrt` and `random` have
no model in the library (#434 is the transcendental one), and a missing
member reads `undefined`, which is honest. Every built-in carries the
`length` 17.1 gives it; `Test/Tarski/FunctionBuiltinsTest.lean` pins the
attributes it carries it with. -/

#guard outcome (expr (.unary .typeof (.ident "Math"))) == "object"
#guard outcome (expr (.member (.ident "Math") "cbrt")) == "undefined"
#guard outcome (expr (.member (.ident "Math") "random")) == "undefined"
#guard outcome (expr (.call (.ident "Math") [])) == "uncaught: TypeError: not a function"
#guard outcome (expr (.new (.ident "Math") [])) == "uncaught: TypeError: not a constructor"
#guard outcome (expr (.member (.member (.ident "Math") "abs") "length")) == "1"
