import Tarski.Eval
import Tarski.Format

/-! `Object.is`, `Object.prototype.hasOwnProperty`, `Object.keys`, and
`Object` as a constructor.

`Object.prototype` exists as of #380 and carries `hasOwnProperty` and
nothing else, so an object literal, a function's `prototype`, an error,
and an array all reach that one method and no other. What is *not* here
is pinned too: there are no descriptors, so `Object.keys` lists every own
key including the ones an engine hides (`prototype` on a function,
`message` on an error), and there is no `Object.prototype.toString`, so
`{} + 1` still throws. Both wait for #389.

`Object.is` is the library's `sameValue`, which is the whole reason the
two zeros and NaN behave as they do. -/

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

/-- `NaN`, which no literal spells and no binding holds until #382. -/
private def nan : Expr := .binary .div (.numLit 0.0) (.numLit 0.0)

/-! ## `Object.is` -/

/-- `Object.is(<args>);` -/
private def objectIs (args : List Expr) : Program :=
  expr (.call (.member (.ident "Object") "is") args)

#guard outcome (objectIs [negZero, negZero]) == "true"
#guard outcome (objectIs [.numLit 0.0, negZero]) == "false"
#guard outcome (objectIs [nan, nan]) == "true"
#guard outcome (objectIs [.strLit "a", .strLit "a"]) == "true"
#guard outcome (objectIs [.numLit 1.0, .strLit "1"]) == "false"
#guard outcome (objectIs [.objectLit [], .objectLit []]) == "false"
-- A missing argument is `undefined`, and `undefined` is itself.
#guard outcome (objectIs []) == "true"

-- `const o = {}; Object.is(o, o);` — objects compare by reference.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.call (.member (.ident "Object") "is") [.ident "o", .ident "o"]) ]
  == "true"

/-! ## `Object.prototype.hasOwnProperty`

Own, not inherited — which is what makes the method invisible to itself
on an instance and visible on the prototype that holds it. An array's
`length` is an own property even though it lives in the object's kind
rather than its property list. -/

-- `const o = { a: 1 }; o.hasOwnProperty("a");`
private def declareO : Stmt :=
  .varDecl .«const» [{ name := "o", init := some (.objectLit [("a", .numLit 1.0)]) }]

/-- `const o = { a: 1 }; o.hasOwnProperty(<key>);` -/
private def oHasOwn (key : Expr) : Program :=
  [declareO, .exprStmt (.call (.member (.ident "o") "hasOwnProperty") [key])]

#guard outcome (oHasOwn (.strLit "a")) == "true"
#guard outcome (oHasOwn (.strLit "b")) == "false"
#guard outcome (oHasOwn (.strLit "hasOwnProperty")) == "false"

-- `Object.prototype.hasOwnProperty("hasOwnProperty");` — the receiver is
-- the object that owns it.
#guard outcome
    (expr (.call (.member (.member (.ident "Object") "prototype") "hasOwnProperty")
      [.strLit "hasOwnProperty"]))
  == "true"

/-- `[1].hasOwnProperty(<key>);` -/
private def arrHasOwn (key : Expr) : Program :=
  expr (.call (.member (.arrayLit [.numLit 1.0]) "hasOwnProperty") [key])

#guard outcome (arrHasOwn (.strLit "length")) == "true"
-- ToPropertyKey turns the index into its string.
#guard outcome (arrHasOwn (.numLit 0.0)) == "true"
#guard outcome (arrHasOwn (.numLit 1.0)) == "false"

/-- `new Error("m").hasOwnProperty(<key>);` — `Error.prototype` chains to
`Object.prototype`, which is how the method is reachable at all. -/
private def errHasOwn (key : Expr) : Program :=
  expr (.call (.member (.new (.ident "Error") [.strLit "m"]) "hasOwnProperty") [key])

#guard outcome (errHasOwn (.strLit "message")) == "true"
#guard outcome (errHasOwn (.strLit "name")) == "false"

-- `const f = Object.prototype.hasOwnProperty; f("a");` — a plain call
-- passes `undefined` as the receiver, which is the only way this slice
-- can hand the method a primitive `this`: `Function.prototype.call` is
-- #389's, and a primitive base has no wrapper prototype to reach it
-- through.
#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some (.member
        (.member (.ident "Object") "prototype") "hasOwnProperty") }],
      .exprStmt (.call (.ident "f") [.strLit "a"]) ]
  == "uncaught: TypeError: Cannot convert a primitive to an object"

/-! ## `Object.keys`

OrdinaryOwnPropertyKeys: integer indices ascending, then everything else
in insertion order. Enumerability is #389's, so an own key an engine
hides is listed here and said to be. -/

/-- `Object.keys(<arg>)<suffix>`. -/
private def keysOf (e : Expr) : Expr := .call (.member (.ident "Object") "keys") [e]

-- `Object.keys({ b: 1, a: 2 }).join();` — insertion order, not sorted.
#guard outcome
    (expr (.call (.member (keysOf (.objectLit [("b", .numLit 1.0), ("a", .numLit 2.0)])) "join") []))
  == "b,a"

-- `const o = { b: 1 }; o[2] = 1; o.a = 1; o[1] = 1; Object.keys(o).join();`
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit [("b", .numLit 1.0)]) }],
      .exprStmt (.assign (.index (.ident "o") (.numLit 2.0)) (.numLit 1.0)),
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 1.0)),
      .exprStmt (.assign (.index (.ident "o") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (.call (.member (keysOf (.ident "o")) "join") []) ]
  == "1,2,b,a"

#guard outcome (expr (.member (keysOf (.objectLit [])) "length")) == "0"

-- `Object.keys([7, 8]).join();` — an array's `length` is not an own
-- property of the property list, so it is not a key.
#guard outcome
    (expr (.call (.member (keysOf (.arrayLit [.numLit 7.0, .numLit 8.0])) "join") []))
  == "0,1"

-- `Object.keys("ab").join();` — a string's own keys are its indices.
#guard outcome (expr (.call (.member (keysOf (.strLit "ab")) "join") [])) == "0,1"

-- `Object.keys(1).length;` — a non-nullish primitive with no own keys.
#guard outcome (expr (.member (keysOf (.numLit 1.0)) "length")) == "0"

#guard outcome (expr (keysOf .undefLit))
  == "uncaught: TypeError: Cannot convert undefined or null to object"
#guard outcome (expr (keysOf .nullLit))
  == "uncaught: TypeError: Cannot convert undefined or null to object"

-- `Object.keys(function f() {}).join();` — pinned as pre-#389: an
-- engine hides `prototype` with an attribute this slice does not have.
#guard outcome
    (expr (.call (.member (keysOf (.funcExpr (some "f") [] [])) "join") []))
  == "prototype"

/-! ## `Object` as a function and as a constructor

Both spellings allocate the same thing, so `new` hands the native no
receiver at all. A primitive other than `undefined` and `null` refuses
until the wrappers land (#382, #391). -/

#guard outcome (expr (.unary .typeof (.call (.ident "Object") []))) == "object"
#guard outcome (expr (.unary .typeof (.call (.ident "Object") [.nullLit]))) == "object"

-- `typeof Object(null).hasOwnProperty;` — the fresh object is linked to
-- `Object.prototype`.
#guard outcome
    (expr (.unary .typeof (.member (.call (.ident "Object") [.nullLit]) "hasOwnProperty")))
  == "function"

-- `const o = {}; Object(o) === o;`
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.binary .strictEq (.call (.ident "Object") [.ident "o"]) (.ident "o")) ]
  == "true"

-- `new Object().constructor === Object;`
#guard outcome
    (expr (.binary .strictEq (.member (.new (.ident "Object") []) "constructor")
      (.ident "Object")))
  == "true"

#guard outcome (expr (.call (.ident "Object") [.numLit 1.0]))
  == "uncaught: TypeError: Cannot convert a primitive to an object"

-- `({}) instanceof Object;`
#guard outcome (expr (.binary .instanceof (.objectLit []) (.ident "Object"))) == "true"

-- `(function () {}) instanceof Object;` — pinned as pre-#389: a function
-- object's own `[[Prototype]]` is still null for want of
-- `Function.prototype`.
#guard outcome
    (expr (.binary .instanceof (.funcExpr none [] []) (.ident "Object")))
  == "false"

#guard outcome (expr (.unary .typeof (.ident "Object"))) == "function"
