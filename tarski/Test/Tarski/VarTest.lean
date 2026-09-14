import Tarski.Eval
import Tarski.Format

/-! `var`: function-scoped, hoisted, and initialized to `undefined`.

`var` is `let`'s opposite on every axis this evaluator models. Its scope
is the enclosing function or script rather than the block it was written
in, so it escapes a block and does not escape a function. Its cell is
created and filled with `undefined` at instantiation rather than at its
declarator, so reading one early answers `undefined` where a `let` would
throw. It may be declared twice, and a bare re-declaration writes
nothing. And it never erases a binding that was already there — a
parameter of the same name, or a global — because instantiation skips a
name that already has a cell. -/

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

/-- `var <name> = <value>;` -/
private def varOf (name : String) (value : Expr) : Stmt :=
  .varDecl .«var» [{ name, init := some value }]

/-- `var <name>;` -/
private def bareVar (name : String) : Stmt := .varDecl .«var» [{ name, init := none }]

/-! ## No dead zone -/

-- `x; var x = 1;` — the read happens before the declarator and answers
-- `undefined`, where a `let` would throw.
#guard outcome [.exprStmt (.ident "x"), varOf "x" (num 1.0)] == "undefined"

-- `typeof v; var v;` — and `typeof` says so too, without throwing.
#guard outcome [.exprStmt (.unary .typeof (.ident "v")), bareVar "v"] == "undefined"

-- `var x = 1; x;` — after the declarator, the value.
#guard outcome [varOf "x" (num 1.0), .exprStmt (.ident "x")] == "1"

/-! ## Function scope, not block scope -/

-- `if (true) { var y = 2; } y;` — a `var` inside a block is the script's.
#guard outcome
    [ .ifStmt (.boolLit true) (.block [varOf "y" (num 2.0)]) none,
      .exprStmt (.ident "y") ]
  == "2"

-- `switch (0) { case 0: var w = 3; } w;` — so is one inside a `switch`
-- clause.
#guard outcome
    [ .switchStmt (num 0.0) [{ test := some (num 0.0), body := [varOf "w" (num 3.0)] }],
      .exprStmt (.ident "w") ]
  == "3"

-- `for (let i = 0; i < 1; i++) { var q = 4; } q;` — and one inside a loop
-- body.
#guard outcome
    [ .forStmt (some (.decl .«let» [{ name := "i", init := some (num 0.0) }]))
        (some (.binary .lt (.ident "i") (num 1.0)))
        (some (.update .inc false (.ident "i")))
        (.block [varOf "q" (num 4.0)]),
      .exprStmt (.ident "q") ]
  == "4"

-- `try { var t = 5; } catch (e) {} t;` — and one inside a `try` block.
#guard outcome
    [ .tryStmt [varOf "t" (num 5.0)] (some { param := some "e", body := [] }) none,
      .exprStmt (.ident "t") ]
  == "5"

-- `function f() { var z = 1; } f(); z;` — but a function's `var`s are its
-- own, so this one does not escape.
#guard outcome
    [ .funcDecl "f" [] [varOf "z" (num 1.0)],
      .exprStmt (.call (.ident "f") []),
      .exprStmt (.ident "z") ]
  == "uncaught: ReferenceError: z is not defined"

-- `{ let s = 1; var s2 = s; } s2;` — a `let` in a block still shadows
-- nothing outside it, and the `var` beside it carries the value out.
#guard outcome
    [ .block
        [ .varDecl .«let» [{ name := "s", init := some (num 1.0) }],
          varOf "s2" (.ident "s") ],
      .exprStmt (.ident "s2") ]
  == "1"

-- `var b = 1; { let b = 2; } b;` — and a block's `let` shadows a `var` for
-- the block and restores it after.
#guard outcome
    [ varOf "b" (num 1.0),
      .block [.varDecl .«let» [{ name := "b", init := some (num 2.0) }]],
      .exprStmt (.ident "b") ]
  == "1"

/-! ## Re-declaration -/

-- `var x = 1; var x; x;` — a bare re-declaration performs no operation,
-- so the value stands.
#guard outcome [varOf "x" (num 1.0), bareVar "x", .exprStmt (.ident "x")] == "1"

-- `var x = 1; var x = 2; x;` — one with an initializer is an assignment.
#guard outcome [varOf "x" (num 1.0), varOf "x" (num 2.0), .exprStmt (.ident "x")] == "2"

-- `function g(a) { var a; return a; } g(5);` — a `var` naming a parameter
-- keeps the argument (10.2.11 step 27).
#guard outcome
    [ .funcDecl "g" ["a"] [bareVar "a", .returnStmt (some (.ident "a"))],
      .exprStmt (.call (.ident "g") [num 5.0]) ]
  == "5"

-- `var f; function f() {} typeof f;` — a function declaration and a `var`
-- of the same name end as the function.
#guard outcome
    [ bareVar "f",
      .funcDecl "f" [] [],
      .exprStmt (.unary .typeof (.ident "f")) ]
  == "function"

/-! ## An existing global stays -/

-- `var print; typeof print;` — a bare `var` naming a global leaves the
-- binding alone rather than resetting it to `undefined` (16.1.7).
#guard outcome [bareVar "print", .exprStmt (.unary .typeof (.ident "print"))] == "function"

-- `var print = 1; print;` — and one with an initializer writes the
-- existing cell rather than shadowing it.
#guard outcome [varOf "print" (num 1.0), .exprStmt (.ident "print")] == "1"

-- `var Error; new TypeError("t") instanceof Error;` — so `Error` is still
-- the constructor and the prototype chain still reaches it.
#guard outcome
    [ bareVar "Error",
      .exprStmt (.binary .instanceof (.new (.ident "TypeError") [.strLit "t"]) (.ident "Error")) ]
  == "true"

/-! ## The value a `var` declaration completes with -/

-- `1; var x = 2;` — a declaration completes empty, `var` included.
#guard outcome [.exprStmt (num 1.0), varOf "x" (num 2.0)] == "1"
