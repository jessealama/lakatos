import Tarski.Eval
import Tarski.Format

/-! Functions, calls, closures, and `this`, against what a JS engine
would print.

Each case is written with the source it models. The programs are the
interesting ones — the issue's own counter, a recursive factorial, two
declarations that call each other — because the value of this file is
that the record says what the semantics are, not that the evaluator
agrees with itself. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-! ## The issue's example

```js
function counter() {
  let n = 0;
  return { next: function () { n = n + 1; return n; } };
}
const c = counter();
c.next(); c.next();
const o = { a: 1 };
o.b = c.next();
typeof o.b === "number" && o.b === 3 && typeof c.next === "function";
```

Three closures over one cell — the two calls above and the one below —
and the cell survives every one of them, which is what the heap-carrying
completion buys: `n = n + 1` runs, then `return n` ends the call
abruptly, and the write is still there. -/
private def counter : Program :=
  [ .funcDecl "counter" []
      [ .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
        .returnStmt (some (.objectLit
          [("next", .funcExpr none []
            [ .exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0))),
              .returnStmt (some (.ident "n")) ])])) ],
    .varDecl .«const» [{ name := "c", init := some (.call (.ident "counter") []) }],
    .exprStmt (.call (.member (.ident "c") "next") []),
    .exprStmt (.call (.member (.ident "c") "next") []),
    .varDecl .«const» [{ name := "o", init := some (.objectLit [("a", .numLit 1.0)]) }],
    .exprStmt (.assign (.member (.ident "o") "b") (.call (.member (.ident "c") "next") [])),
    .exprStmt (.logical .and
      (.logical .and
        (.binary .strictEq (.unary .typeof (.member (.ident "o") "b")) (.strLit "number"))
        (.binary .strictEq (.member (.ident "o") "b") (.numLit 3.0)))
      (.binary .strictEq (.unary .typeof (.member (.ident "c") "next")) (.strLit "function"))) ]

#guard outcome counter == "true"

/-! ## Recursion -/

-- `function fact(n) { return n <= 1 ? 1 : n * fact(n - 1); } fact(5);`
#guard outcome
    [ .funcDecl "fact" ["n"]
        [ .returnStmt (some (.cond (.binary .le (.ident "n") (.numLit 1.0)) (.numLit 1.0)
            (.binary .mul (.ident "n")
              (.call (.ident "fact") [.binary .sub (.ident "n") (.numLit 1.0)])))) ],
      .exprStmt (.call (.ident "fact") [.numLit 5.0]) ]
  == "120"

-- `function a(n) { return n === 0 ? "done" : b(n - 1); }
--  function b(n) { return a(n); }
--  a(4);`
-- Mutual recursion where `a` names `b` above `b`'s own text: both cells
-- are allocated and both functions built before either statement runs.
#guard outcome
    [ .funcDecl "a" ["n"]
        [ .returnStmt (some (.cond (.binary .strictEq (.ident "n") (.numLit 0.0))
            (.strLit "done") (.call (.ident "b") [.binary .sub (.ident "n") (.numLit 1.0)]))) ],
      .funcDecl "b" ["n"] [.returnStmt (some (.call (.ident "a") [.ident "n"]))],
      .exprStmt (.call (.ident "a") [.numLit 4.0]) ]
  == "done"

-- `const f = function fac(n) { return n <= 1 ? 1 : n * fac(n - 1); }; f(4);`
-- A named function expression binds its own name inside itself, and
-- nowhere else.
#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some (.funcExpr (some "fac") ["n"]
        [ .returnStmt (some (.cond (.binary .le (.ident "n") (.numLit 1.0)) (.numLit 1.0)
            (.binary .mul (.ident "n")
              (.call (.ident "fac") [.binary .sub (.ident "n") (.numLit 1.0)])))) ]) }],
      .exprStmt (.call (.ident "f") [.numLit 4.0]) ]
  == "24"

-- `const f = function fac() { return 1; }; fac;` — and the name does not
-- escape.
private def named : Expr :=
  .funcExpr (some "fac") [] [.returnStmt (some (.numLit 1.0))]

#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some named }],
      .exprStmt (.ident "fac") ]
  == "uncaught: ReferenceError: fac is not defined"

/-! ## `this` -/

-- `const o = { v: 7, m: function () { return this.v; } }; o.m();`
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit
        [ ("v", .numLit 7.0),
          ("m", .funcExpr none [] [.returnStmt (some (.member .this "v"))]) ]) }],
      .exprStmt (.call (.member (.ident "o") "m") []) ]
  == "7"

-- `const o = { v: 7, m: function () { const g = () => this.v; return g(); } }; o.m();`
-- An arrow pushes no `this`, so the one it sees is the method's.
private def arrowThis : Expr := .arrow [] (.expr (.member .this "v"))

private def lexicalThis : Expr :=
  .funcExpr none []
    [ .varDecl .«const» [{ name := "g", init := some arrowThis }],
      .returnStmt (some (.call (.ident "g") [])) ]

private def holder : Expr := .objectLit [("v", .numLit 7.0), ("m", lexicalThis)]

#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some holder }],
      .exprStmt (.call (.member (.ident "o") "m") []) ]
  == "7"

-- `const f = function () { return this; }; f();` — strict mode, so a
-- plain call has no receiver.
private def returnThis : Expr := .funcExpr none [] [.returnStmt (some .this)]

#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some returnThis }],
      .exprStmt (.call (.ident "f") []) ]
  == "undefined"

-- `this;` at the top level. `undefined` until #389 gives the script a
-- global object; an engine answers `undefined` for a module and the
-- global object for a script, and neither exists here yet.
#guard outcome [.exprStmt .this] == "undefined"

/-! ## Argument binding and completion values -/

-- `function f(a, b) { return b; } f(1);` — a missing argument is
-- `undefined`.
#guard outcome
    [ .funcDecl "f" ["a", "b"] [.returnStmt (some (.ident "b"))],
      .exprStmt (.call (.ident "f") [.numLit 1.0]) ]
  == "undefined"

-- `function f(a) { return a; } f(1, 2);` — an extra one is dropped.
#guard outcome
    [ .funcDecl "f" ["a"] [.returnStmt (some (.ident "a"))],
      .exprStmt (.call (.ident "f") [.numLit 1.0, .numLit 2.0]) ]
  == "1"

-- `function f() {} f();` — a body without a `return` answers `undefined`.
#guard outcome [.funcDecl "f" [] [], .exprStmt (.call (.ident "f") [])] == "undefined"

-- `function f() { return; } f();` — as does a bare `return`.
#guard outcome
    [.funcDecl "f" [] [.returnStmt none], .exprStmt (.call (.ident "f") [])] == "undefined"

-- `1; function f() {}` — a function declaration completes empty, so the
-- script's completion value is still 1.
#guard outcome [.exprStmt (.numLit 1.0), .funcDecl "f" [] []] == "1"

-- `{ function f() {} } f();` — and a function declared in a block is not
-- visible after it.
#guard outcome
    [ .block [.funcDecl "f" [] [.returnStmt (some (.numLit 1.0))]],
      .exprStmt (.call (.ident "f") []) ]
  == "uncaught: ReferenceError: f is not defined"

/-! ## What is not callable -/

-- `const n = 1; n();`
#guard outcome
    [ .varDecl .«const» [{ name := "n", init := some (.numLit 1.0) }],
      .exprStmt (.call (.ident "n") []) ]
  == "uncaught: TypeError: not a function"

-- `const o = {}; o();` — an object without a `[[Call]]`.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.call (.ident "o") []) ]
  == "uncaught: TypeError: not a function"

-- `const f = () => 1; new f();` — an arrow has no `[[Construct]]`.
#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some (.arrow [] (.expr (.numLit 1.0))) }],
      .exprStmt (.new (.ident "f") []) ]
  == "uncaught: TypeError: not a constructor"

/-! ## Short-circuiting

`&&` and `||` answer with one of their operands, and do not evaluate the
one they do not need — which is observable, because the other one
throws. -/

-- `false && undeclared;`
#guard outcome [.exprStmt (.logical .and (.boolLit false) (.ident "undeclared"))] == "false"

-- `true || undeclared;`
#guard outcome [.exprStmt (.logical .or (.boolLit true) (.ident "undeclared"))] == "true"

-- `0 || "fallback";` — the value is the operand, not a boolean.
#guard outcome [.exprStmt (.logical .or (.numLit 0.0) (.strLit "fallback"))] == "fallback"
