import Tarski.Eval
import Tarski.Format

/-! The `arguments` object.

The epic is strict-mode only, so there is one kind of it:
CreateUnmappedArgumentsObject's. Unmapped is the whole of what the cases
below are about — writing `arguments[0]` does not move the parameter and
writing the parameter does not move `arguments[0]` — together with the
three things around it: `length` is the *argument* count rather than the
parameter count, `callee` is an accessor whose getter and setter are both
`%ThrowTypeError%`, and an arrow has no `arguments` of its own, so one
inside an arrow is the enclosing function's and one at top level resolves
nowhere.

That a function which never spells the name allocates no object at all is
not observable from JavaScript — `eval` and the `Function` constructor,
the two ways to observe it, are outside this epic — so it has no case
here; `Test/Tarski/CallSimpTest.lean`'s unchanged proof is its pin. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def num (x : Float) : Expr := .numLit x

/-- `arguments` -/
private def args : Expr := .ident "arguments"

/-- `arguments[<i>]` -/
private def arg (i : Float) : Expr := .index args (num i)

/-- `function f(<params>) { <body> } f(<call>);` -/
private def callF (params : List Param) (body : List Stmt) (call : List Expr) : Program :=
  [ .funcDecl "f" params body, .exprStmt (.call (.ident "f") call) ]

/-! ## The issue's example

A hoisted function read by `typeof` ahead of its own text,
`arguments.length` inside it, a labelled `continue` out of a `switch`,
and the script-level dead zone caught as a `ReferenceError`. -/

/-- ```js
"use strict";
function f() {
  const before = typeof g;   // "function": declarations hoist
  function g() { return arguments.length; }
  let r = "";
  outer: for (let i = 0; i < 3; i++) {
    switch (i) { case 1: continue outer; default: r = r + i; }
  }
  return before === "function" && g(1, 2, 3) === 3 && r === "02";
}
let tdz = false;
try { x; } catch (e) { tdz = e instanceof ReferenceError; }
let x = 1;
f() && tdz;
``` -/
private def issueExample : Program :=
  [ .funcDecl "f" []
      [ .varDecl .«const» [{ name := "before", init := some (.unary .typeof (.ident "g")) }],
        .funcDecl "g" [] [.returnStmt (some (.member args "length"))],
        .varDecl .«let» [{ name := "r", init := some (.strLit "") }],
        .labeled "outer"
          (.forStmt (some (.decl .«let» [{ name := "i", init := some (num 0.0) }]))
            (some (.binary .lt (.ident "i") (num 3.0)))
            (some (.update .inc false (.ident "i")))
            (.block
              [ .switchStmt (.ident "i")
                  [ { test := some (num 1.0), body := [.continueStmt (some "outer")] },
                    { test := none,
                      body :=
                        [ .exprStmt (.assign (.ident "r")
                            (.binary .add (.ident "r") (.ident "i"))) ] } ] ])),
        .returnStmt (some
          (.logical .and
            (.logical .and
              (.binary .strictEq (.ident "before") (.strLit "function"))
              (.binary .strictEq
                (.call (.ident "g") [num 1.0, num 2.0, num 3.0]) (num 3.0)))
            (.binary .strictEq (.ident "r") (.strLit "02")))) ],
    .varDecl .«let» [{ name := "tdz", init := some (.boolLit false) }],
    .tryStmt [.exprStmt (.ident "x")]
      (some { param := some "e",
              body :=
                [ .exprStmt (.assign (.ident "tdz")
                    (.binary .instanceof (.ident "e") (.ident "ReferenceError"))) ] })
      none,
    .varDecl .«let» [{ name := "x", init := some (num 1.0) }],
    .exprStmt (.logical .and (.call (.ident "f") []) (.ident "tdz")) ]

#guard outcome issueExample == "true"

/-! ## `length` is the argument count -/

-- `function f() { return arguments.length; } f(1, 2, 3);`
#guard outcome (callF [] [.returnStmt (some (.member args "length"))]
    [num 1.0, num 2.0, num 3.0])
  == "3"

-- `function f() { return arguments.length; } f();` — no arguments, not
-- the parameter count.
#guard outcome (callF [] [.returnStmt (some (.member args "length"))] []) == "0"

-- `function f(a, b) { return arguments.length; } f(1);` — nor the
-- parameter count when there are parameters.
#guard outcome (callF ["a", "b"] [.returnStmt (some (.member args "length"))] [num 1.0])
  == "1"

/-! ## Indices -/

-- `function f(a) { return arguments[0] + ":" + arguments[1]; } f(1);` —
-- past the end is an absent property, which reads as `undefined`.
#guard outcome
    (callF ["a"]
      [.returnStmt (some (.binary .add (.binary .add (arg 0.0) (.strLit ":")) (arg 1.0)))]
      [num 1.0])
  == "1:undefined"

/-! ## Unmapped, in both directions

A strict `arguments` has no `[[ParameterMap]]`, so neither half of the
pair moves when the other is written. -/

-- `function f(a) { arguments[0] = 2; return a; } f(1);`
#guard outcome
    (callF ["a"]
      [ .exprStmt (.assign (.index args (num 0.0)) (num 2.0)),
        .returnStmt (some (.ident "a")) ]
      [num 1.0])
  == "1"

-- `function f(a) { a = 2; return arguments[0]; } f(1);`
#guard outcome
    (callF ["a"]
      [ .exprStmt (.assign (.ident "a") (num 2.0)),
        .returnStmt (some (arg 0.0)) ]
      [num 1.0])
  == "1"

/-! ## An arrow has none of its own -/

-- `function f() { return (() => arguments[0])(); } f(7);` — the arrow
-- pushes no binding, so the name resolves outward to the function's.
#guard outcome
    (callF [] [.returnStmt (some (.call (.arrow [] (.expr (arg 0.0))) []))] [num 7.0])
  == "7"

-- `(() => arguments)();` — at top level there is nothing to resolve to.
#guard outcome [.exprStmt (.call (.arrow [] (.expr args)) [])]
  == "uncaught: ReferenceError: arguments is not defined"

/-! ## A method and a class constructor bind it -/

-- `class A { constructor() { this.n = arguments.length; }
--            m() { return arguments.length; } }
--  new A(1, 2).n + new A().m(3);`
#guard outcome
    [ .classDecl "A"
        { name := some "A", superClass := none,
          elements :=
            [ .ctor []
                [ .exprStmt (.assign (.member .this "n") (.member args "length")) ],
              .method .method false "m" []
                [ .returnStmt (some (.member args "length")) ] ] },
      .exprStmt (.binary .add
        (.member (.new (.ident "A") [num 1.0, num 2.0]) "n")
        (.call (.member (.new (.ident "A") []) "m") [num 3.0])) ]
  == "3"

/-! ## `callee` -/

private def calleeMessage : String :=
  "uncaught: TypeError: 'caller', 'callee', and 'arguments' properties may not be " ++
    "accessed on strict mode functions or the arguments objects for calls to them"

-- `function f() { return arguments.callee; } f();`
#guard outcome (callF [] [.returnStmt (some (.member args "callee"))] []) == calleeMessage

-- `function f() { arguments.callee = 1; } f();` — the setter is the same
-- object as the getter, so a write raises the same error.
#guard outcome
    (callF [] [.exprStmt (.assign (.member args "callee") (num 1.0))] [])
  == calleeMessage

/-! ## What it looks like from outside -/

-- `function f() { return typeof arguments; } f();`
#guard outcome (callF [] [.returnStmt (some (.unary .typeof args))] []) == "object"

-- `function f() { return Object.keys(arguments).join(); } f(1, 2);` —
-- the indices alone: 10.4.4.7 makes `length` and `callee`
-- non-enumerable, and only the arguments themselves are ordinary data
-- properties.
#guard outcome
    (callF []
      [ .returnStmt (some (.call
          (.member (.call (.member (.ident "Object") "keys") [args]) "join") [])) ]
      [num 1.0, num 2.0])
  == "0,1"
