import Tarski.Eval
import Tarski.Format

/-! `Function.prototype` and what every function now carries.

The issue's own example is the first case here: a non-writable property
refusing a strict-mode write, its descriptor read back, `Object.keys`
hiding it, and `call` and `bind` giving a function its `this`.

A function's `length` and `name` are non-writable, non-enumerable, and
configurable, which is the shape test262's `propertyHelper.js` verifies
on every built-in; NamedEvaluation is what decides the `name` when the
function is anonymous. `Function.prototype.toString` answers the
NativeFunction form for every function, the bridge keeping no source
text; the `Function` constructor exists as an object and refuses to be
called. -/

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

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ target := n, init := some e }]

/-- `<f>.<method>(<args>)`. -/
private def invoke (f : Expr) (method : String) (args : List Expr) : Expr :=
  .call (.member f method) args

/-- `function () {}`, anonymous and empty. -/
private def anon : Expr := .funcExpr none [] []

/-- `{ k: <v> }`, the receiver the issue's example binds. -/
private def receiver (v : Float) : Expr := .objectLit [.init "k" (.numLit v)]

/-! ## The issue's example

```js
const o = {};
Object.defineProperty(o, "x",
  { value: 1, writable: false, enumerable: false, configurable: false });
let threw = false;
try { o.x = 2; } catch (e) { threw = e instanceof TypeError; }
const d = Object.getOwnPropertyDescriptor(o, "x");
function f(a, b) { return this.k + a + b; }
threw && d.writable === false && Object.keys(o).length === 0
  && f.call({ k: 1 }, 2, 3) === 6 && f.bind({ k: 10 })(1, 1) === 12;
```
-/

private def issueExample : Program :=
  [ «let» "o" (.objectLit []),
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [ .ident "o", .strLit "x",
        .objectLit [.init "value" (.numLit 1.0), .init "writable" (.boolLit false),
                    .init "enumerable" (.boolLit false), .init "configurable" (.boolLit false)] ]),
    .varDecl .«let» [{ target := "threw", init := some (.boolLit false) }],
    .tryStmt [.exprStmt (.assign (.member (.ident "o") "x") (.numLit 2.0))]
      (some { param := some "e",
              body := [.exprStmt (.assign (.ident "threw")
                (.binary .instanceof (.ident "e") (.ident "TypeError")))] })
      none,
    «let» "d" (.call (.member (.ident "Object") "getOwnPropertyDescriptor")
      [.ident "o", .strLit "x"]),
    .funcDecl "f" ["a", "b"]
      [.returnStmt (some (.binary .add
        (.binary .add (.member .this "k") (.ident "a")) (.ident "b")))],
    .exprStmt (.logical .and
      (.logical .and
        (.logical .and
          (.logical .and (.ident "threw")
            (.binary .strictEq (.member (.ident "d") "writable") (.boolLit false)))
          (.binary .strictEq
            (.member (.call (.member (.ident "Object") "keys") [.ident "o"]) "length")
            (.numLit 0.0)))
        (.binary .strictEq
          (invoke (.ident "f") "call" [receiver 1.0, .numLit 2.0, .numLit 3.0])
          (.numLit 6.0)))
      (.binary .strictEq
        (.call (invoke (.ident "f") "bind" [receiver 10.0]) [.numLit 1.0, .numLit 1.0])
        (.numLit 12.0))) ]

#guard outcome issueExample == "true"

/-! ## `call`

The receiver is the first argument and the rest are the call's; a
missing first argument is `undefined`, which strict mode leaves alone. -/

/-- `function () { return typeof this; }`. -/
private def typeofThis : Expr := .funcExpr none [] [.returnStmt (some (.unary .typeof .this))]

#guard outcome (expr (invoke typeofThis "call" [])) == "undefined"
#guard outcome (expr (invoke (.funcExpr none ["a"] [.returnStmt (some (.ident "a"))])
    "call" [.undefLit, .numLit 5.0]))
  == "5"
#guard outcome (expr (.member (.member (.member (.ident "Function") "prototype") "call") "length"))
  == "1"

/-! ## `apply`

A nullish argument list is empty, an array-like is read through
`Get`, and anything else is CreateListFromArrayLike's refusal. -/

/-- `function (a, b) { return a + b; }`. -/
private def plus : Expr :=
  .funcExpr none ["a", "b"] [.returnStmt (some (.binary .add (.ident "a") (.ident "b")))]

#guard outcome (expr (invoke plus "apply" [.undefLit, .arrayLit [.numLit 1.0, .numLit 2.0]]))
  == "3"
#guard outcome (expr (invoke plus "apply" [.undefLit])) == "NaN"
#guard outcome (expr (invoke plus "apply" [.undefLit, .nullLit])) == "NaN"
#guard outcome
    [ «let» "like" (.objectLit []),
      .exprStmt (.assign (.member (.ident "like") "length") (.numLit 2.0)),
      .exprStmt (.assign (.index (.ident "like") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (.assign (.index (.ident "like") (.numLit 1.0)) (.numLit 2.0)),
      .exprStmt (invoke plus "apply" [.undefLit, .ident "like"]) ]
  == "3"
#guard outcome (expr (invoke plus "apply" [.undefLit, .numLit 1.0]))
  == "uncaught: TypeError: CreateListFromArrayLike called on non-object"
#guard outcome (expr (invoke (.member (.member (.ident "Function") "prototype") "apply")
    "call" [.objectLit []]))
  == ("uncaught: TypeError: Function.prototype.apply was called on [object Object], " ++
      "which is not a function")

/-! ## `bind`

A bound function is a `Callable` of its own: calling it calls the
target, constructing it constructs the target, and `instanceof` follows
it. Its `length` is the target's less the bound arguments, never below
zero, and its `name` is `"bound "` and the target's. -/

#guard outcome (expr (.call (invoke plus "bind" [.undefLit, .numLit 1.0]) [.numLit 2.0])) == "3"
#guard outcome (expr (.unary .typeof (invoke anon "bind" []))) == "function"
#guard outcome (expr (.call (invoke (invoke plus "bind" [.undefLit, .numLit 1.0]) "bind" [])
    [.numLit 2.0]))
  == "3"
#guard outcome (expr (.member (invoke (.funcExpr none ["a", "b", "c"] []) "bind"
    [.nullLit, .numLit 1.0]) "length"))
  == "2"
#guard outcome (expr (.member (invoke (.arrow [] (.expr (.numLit 1.0))) "bind" []) "length"))
  == "0"

/-- `function f() {} Object.defineProperty(f, "length", <desc>); f.bind(null, 1).length` —
step 6 reads the target's own `length` with Get, so an accessor runs, and
an infinite length stays infinite rather than clamping to zero. -/
private def boundLengthOf (desc : List PropDef) : Program :=
  [ .funcDecl "f" [] [],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [.ident "f", .strLit "length", .objectLit desc]),
    .exprStmt (.member (invoke (.ident "f") "bind" [.nullLit, .numLit 1.0]) "length") ]

#guard outcome (boundLengthOf [.init "value" (.ident "Infinity")]) == "Infinity"
#guard outcome (boundLengthOf [.init "value" (.unary .neg (.ident "Infinity"))]) == "0"
#guard outcome (boundLengthOf [.init "value" (.numLit 3.5)]) == "2"
#guard outcome (boundLengthOf [.init "value" (.strLit "3")]) == "0"
#guard outcome (boundLengthOf [.init "get" (.arrow [] (.expr (.numLit 5.0)))]) == "4"
#guard outcome (expr (.member (invoke (.funcExpr (some "f") [] []) "bind" []) "name"))
  == "bound f"
#guard outcome (expr (.member (invoke (invoke (.funcExpr (some "f") [] []) "bind" []) "bind" [])
    "name"))
  == "bound bound f"
#guard outcome (expr (.member (invoke anon "bind" []) "name")) == "bound "
#guard outcome (expr (invoke (.member (.member (.ident "Function") "prototype") "bind")
    "call" [.objectLit []]))
  == "uncaught: TypeError: Bind must be called on a function"

-- `new (F.bind(null, 1))(2)`: the target constructs, so the instance is
-- an `F` and the bound argument comes first.
#guard outcome
    [ .funcDecl "F" ["a", "b"]
        [ .exprStmt (.assign (.member .this "s")
            (.binary .add (.ident "a") (.ident "b"))) ],
      «let» "B" (invoke (.ident "F") "bind" [.nullLit, .numLit 1.0]),
      .exprStmt (.member (.new (.ident "B") [.numLit 2.0]) "s") ]
  == "3"
#guard outcome
    [ .funcDecl "F" [] [],
      «let» "B" (invoke (.ident "F") "bind" [.nullLit]),
      .exprStmt (.binary .instanceof (.new (.ident "B") []) (.ident "F")) ]
  == "true"
-- An arrow has no `[[Construct]]`, and neither does a function bound
-- from one.
#guard outcome (expr (.new (invoke (.arrow [] (.expr (.numLit 1.0))) "bind" []) []))
  == "uncaught: TypeError: not a constructor"

/-! ## `Function.prototype` itself, and `Function`

`Function.prototype` is callable and answers `undefined`; `Function` is
an object whose `prototype` every function chains to, and calling it is
out of the epic's scope. -/

#guard outcome (expr (.call (.member (.ident "Function") "prototype") [])) == "undefined"
#guard outcome (expr (.unary .typeof (.ident "Function"))) == "function"
#guard outcome (expr (.member (.ident "Function") "length")) == "1"
#guard outcome (expr (.binary .instanceof anon (.ident "Function"))) == "true"
#guard outcome (expr (.binary .strictEq
    (.call (.member (.ident "Object") "getPrototypeOf")
      [.classExpr { name := none, superClass := none, elements := [] }])
    (.member (.ident "Function") "prototype")))
  == "true"

-- `Function(...)` is a decoder refusal; an alias escapes that and meets
-- the runtime row.
#guard outcome [«let» "F" (.ident "Function"), .exprStmt (.call (.ident "F") [.strLit "x"])]
  == "uncaught: TypeError: Function constructor is out of scope"

/-! ## `toString`

The NativeFunction form for every function — native, closure, and bound
alike — and a `TypeError` off a function, which is what test262 checks
without a source text. -/

#guard outcome (expr (.call (.ident "String") [.funcExpr (some "f") ["a"] []]))
  == "function f() { [native code] }"
#guard outcome (expr (.call (.ident "String") [.ident "parseInt"]))
  == "function parseInt() { [native code] }"
#guard outcome (expr (invoke (.member (.member (.ident "Function") "prototype") "toString")
    "call" [.objectLit []]))
  == "uncaught: TypeError: Function.prototype.toString requires that 'this' be a Function"

/-! ## `length` and `name`, and the attributes they carry

Every built-in has the `length` 17.1 gives it; a closure's is its
parameter count. Both are non-writable and configurable, so a write
refuses and a definition succeeds — which is exactly what
`propertyHelper.js` verifies. -/

#guard outcome (expr (.member (.member (.ident "Math") "abs") "length")) == "1"
#guard outcome (expr (.member (.ident "parseInt") "length")) == "2"
#guard outcome (expr (.member (.funcExpr none ["a", "b"] []) "length")) == "2"

#guard outcome [.funcDecl "f" [] [], .exprStmt (.assign (.member (.ident "f") "name")
    (.strLit "x"))]
  == "uncaught: TypeError: Cannot assign to read only property 'name' of object '#<Object>'"
#guard outcome
    [ .funcDecl "f" [] [],
      .exprStmt (.call (.member (.ident "Object") "defineProperty")
        [.ident "f", .strLit "name", .objectLit [.init "value" (.strLit "x")]]),
      .exprStmt (.member (.ident "f") "name") ]
  == "x"
#guard outcome (expr (.call (.member (.funcExpr (some "f") [] []) "propertyIsEnumerable")
    [.strLit "prototype"]))
  == "false"

/-! ## NamedEvaluation

The four places the specification gives an anonymous function a name;
everything else is named the empty string. -/

#guard outcome [.funcDecl "f" [] [], .exprStmt (.member (.ident "f") "name")] == "f"
#guard outcome (expr (.member (.funcExpr (some "g") [] []) "name")) == "g"
#guard outcome [«let» "h" (.arrow [] (.expr (.numLit 1.0))),
                .exprStmt (.member (.ident "h") "name")]
  == "h"
#guard outcome (expr (.member (.member (.objectLit [.init "m" (anon)]) "m") "name")) == "m"
#guard outcome
    [ .classDecl "A"
        { name := some "A", superClass := none,
          elements := [.field false (.«public» "x") (some (.arrow [] (.expr (.numLit 1.0))))] },
      .exprStmt (.member (.member (.new (.ident "A") []) "x") "name") ]
  == "x"
#guard outcome
    [ .varDecl .«let» [{ target := "k", init := none }],
      .exprStmt (.assign (.ident "k") anon),
      .exprStmt (.member (.ident "k") "name") ]
  == "k"
#guard outcome (expr (.member anon "name")) == ""
#guard outcome (expr (.call (.funcExpr none ["a"] [.returnStmt (some (.member (.ident "a") "name"))])
    [anon]))
  == ""

-- A class, a method, and an accessor half each take the spelling
-- 15.4.4 gives them.
#guard outcome
    [ .classDecl "A"
        { name := some "A", superClass := none,
          elements := [.method .getter false "x" [] [.returnStmt (some (.numLit 1.0))]] },
      .exprStmt (.member (.member (.call (.member (.ident "Object") "getOwnPropertyDescriptor")
        [.member (.ident "A") "prototype", .strLit "x"]) "get") "name") ]
  == "get x"
#guard outcome
    [ .classDecl "A"
        { name := some "A", superClass := none,
          elements := [.method .method false "m" [] []] },
      .exprStmt (.member (.member (.member (.ident "A") "prototype") "m") "name") ]
  == "m"
#guard outcome [.classDecl "A" { name := some "A", superClass := none, elements := [] },
                .exprStmt (.member (.ident "A") "name")]
  == "A"
#guard outcome
    [ «let» "B" (.classExpr { name := none, superClass := none, elements := [] }),
      .exprStmt (.member (.ident "B") "name") ]
  == "B"
