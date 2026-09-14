import Tarski.Eval
import Tarski.Format

/-! What the test262 harness files execute, run as programs.

This is #380's own measure: the string and array operations the harness
needs, exercised by the harness's own code rather than by cases invented
here. Two pieces are transcribed.

`harness/sta.js` runs verbatim — it needs nothing this slice does not
have — and defines `Test262Error`, its `thrower`, its `prototype.toString`,
and `$DONOTEVALUATE`. `harness/compareArray.js` is a deprecated empty
file upstream; the `compareArray` the suite actually calls lives inside
`harness/assert.js`, and it is transcribed here with `let` and `while`
where the original writes `for (var i = 0; …)`, because `for` is #383's
and `var` is #393's, and with a standalone `isSameValue` where the
original calls `assert._isSameValue`, because `assert` itself needs
`switch` (#393), `Object.prototype.toString.call` (#389),
`Array.prototype.map.call` (#390), and `JSON` (#392). Assembling the
real harness files behind a runner is #381's; what this file pins is that
the operations they call are here and answer correctly.

test262 is BSD-licensed; the two transcriptions are of code from that
suite. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-! ## `harness/sta.js`

```js
function Test262Error(message) {
  if (!(this instanceof Test262Error)) {
    return new Test262Error(message);
  }
  this.message = message || "";
}

Test262Error.thrower = function (message) {
  throw new Test262Error(message);
};

Test262Error.prototype.toString = function () {
  return "Test262Error: " + this.message;
};

function $DONOTEVALUATE() {
  throw "Test262: This statement should not be evaluated.";
}
```
-/

private def sta : List Stmt :=
  [ .funcDecl "Test262Error" ["message"]
      [ .ifStmt (.unary .not (.binary .instanceof .this (.ident "Test262Error")))
          (.block [.returnStmt (some (.new (.ident "Test262Error") [.ident "message"]))])
          none,
        .exprStmt (.assign (.member .this "message")
          (.logical .or (.ident "message") (.strLit ""))) ],
    .exprStmt (.assign (.member (.ident "Test262Error") "thrower")
      (.funcExpr none ["message"]
        [.throwStmt (.new (.ident "Test262Error") [.ident "message"])])),
    .exprStmt (.assign (.member (.member (.ident "Test262Error") "prototype") "toString")
      (.funcExpr none []
        [.returnStmt (some (.binary .add (.strLit "Test262Error: ")
          (.member .this "message")))])),
    .funcDecl "$DONOTEVALUATE" []
      [.throwStmt (.strLit "Test262: This statement should not be evaluated.")] ]

/-! ```js
try {
  Test262Error.thrower("m");
} catch (e) {
  e instanceof Test262Error &&
    e.toString() === "Test262Error: m" &&
    Test262Error("x") instanceof Test262Error &&
    new Test262Error().message === "";
}
```

The third conjunct is the `instanceof` guard doing its work: called as a
function in strict mode the receiver is `undefined`, so the constructor
calls itself with `new`. -/

#guard outcome
    (sta ++
      [ .tryStmt
          [.exprStmt (.call (.member (.ident "Test262Error") "thrower") [.strLit "m"])]
          (some { param := some "e",
                  body := [.exprStmt (.logical .and
                    (.logical .and
                      (.logical .and
                        (.binary .instanceof (.ident "e") (.ident "Test262Error"))
                        (.binary .strictEq (.call (.member (.ident "e") "toString") [])
                          (.strLit "Test262Error: m")))
                      (.binary .instanceof (.call (.ident "Test262Error") [.strLit "x"])
                        (.ident "Test262Error")))
                    (.binary .strictEq
                      (.member (.new (.ident "Test262Error") []) "message") (.strLit "")))] })
          none ])
  == "true"

/-! `$DONOTEVALUATE();` throws a string, which the binary prints as
itself rather than as `<name>: <message>`. -/
#guard outcome (sta ++ [.exprStmt (.call (.ident "$DONOTEVALUATE") [])])
  == "uncaught: Test262: This statement should not be evaluated."

/-! ## The harness's `compareArray`

```js
function isSameValue(a, b) {
  if (a === b) {
    return a !== 0 || 1 / a === 1 / b;
  }
  return a !== a && b !== b;
}

function compareArray(a, b) {
  if (b.length !== a.length) {
    return false;
  }
  let i = 0;
  while (i < a.length) {
    if (!isSameValue(b[i], a[i])) {
      return false;
    }
    i = i + 1;
  }
  return true;
}
```
-/

private def compareArray : List Stmt :=
  [ .funcDecl "isSameValue" ["a", "b"]
      [ .ifStmt (.binary .strictEq (.ident "a") (.ident "b"))
          (.block [.returnStmt (some (.logical .or
            (.binary .strictNe (.ident "a") (.numLit 0.0))
            (.binary .strictEq
              (.binary .div (.numLit 1.0) (.ident "a"))
              (.binary .div (.numLit 1.0) (.ident "b")))))])
          none,
        .returnStmt (some (.logical .and
          (.binary .strictNe (.ident "a") (.ident "a"))
          (.binary .strictNe (.ident "b") (.ident "b")))) ],
    .funcDecl "compareArray" ["a", "b"]
      [ .ifStmt (.binary .strictNe (.member (.ident "b") "length")
          (.member (.ident "a") "length"))
          (.block [.returnStmt (some (.boolLit false))]) none,
        .varDecl .«let» [{ name := "i", init := some (.numLit 0.0) }],
        .whileStmt (.binary .lt (.ident "i") (.member (.ident "a") "length"))
          (.block
            [ .ifStmt (.unary .not (.call (.ident "isSameValue")
                [ .index (.ident "b") (.ident "i"),
                  .index (.ident "a") (.ident "i") ]))
                (.block [.returnStmt (some (.boolLit false))]) none,
              .exprStmt (.assign (.ident "i")
                (.binary .add (.ident "i") (.numLit 1.0))) ]),
        .returnStmt (some (.boolLit true)) ] ]

/-- An array literal of number literals. -/
private def nums (xs : List Float) : Expr := .arrayLit (xs.map (.numLit ·))

/-- `compareArray(<a>, <b>)`. -/
private def compare (a b : Expr) : Expr := .call (.ident "compareArray") [a, b]

/-- `NaN`, the global binding. No literal spells it. -/
private def nan : Expr := .ident "NaN"

/-! ```js
compareArray([1, 2, 3], [1, 2, 3]) &&
  !compareArray([1, 2], [1, 2, 3]) &&
  !compareArray([1, 2, 3], [1, 2, 4]) &&
  compareArray([0 / 0], [0 / 0]) &&
  !compareArray([0], [-0]) &&
  compareArray([], []);
```

The last three are why the harness has an `isSameValue` of its own
rather than `===`: two NaNs are the same value, and the two zeros are
not. -/

#guard outcome
    (compareArray ++
      [ .exprStmt (.logical .and
          (.logical .and
            (.logical .and
              (.logical .and
                (.logical .and
                  (compare (nums [1.0, 2.0, 3.0]) (nums [1.0, 2.0, 3.0]))
                  (.unary .not (compare (nums [1.0, 2.0]) (nums [1.0, 2.0, 3.0]))))
                (.unary .not (compare (nums [1.0, 2.0, 3.0]) (nums [1.0, 2.0, 4.0]))))
              (compare (.arrayLit [nan]) (.arrayLit [nan])))
            (.unary .not (compare (nums [0.0]) (.arrayLit [.unary .neg (.numLit 0.0)]))))
          (compare (.arrayLit []) (.arrayLit []))) ])
  == "true"
