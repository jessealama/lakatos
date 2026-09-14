import Tarski.Eval
import Tarski.Format

/-! The `for` statement, head by head.

The head is three optional parts and four spellings of the first one, and
each combination changes what is in scope after the loop and what a
closure made inside it captures. The per-iteration binding is the case
worth the most: `for (let i = …)` gives every iteration a cell of its
own, copied after the body and before the update, so a function the body
built keeps the value the body saw. `const` and `var` heads do not, and
`var` is not even the loop's — it belongs to the function around it. -/

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
private def i : Expr := .ident "i"

/-- `i < n`, the ordinary head test. -/
private def below (n : Float) : Expr := .binary .lt i (num n)

/-- `i++`, the ordinary head update. -/
private def bump : Expr := .update .inc false (.ident "i")

/-- `for (<kind> i = 0; i < n; i++) body`. -/
private def counting (kind : DeclKind) (n : Float) (body : Stmt) : Stmt :=
  .forStmt (some (.decl kind [{ target := "i", init := some (num 0.0) }]))
    (some (below n)) (some bump) body

/-! ## What the head leaves behind -/

-- `for (var i = 0; i < 3; i++) {} i;` — a `var` head is the function's,
-- so it is still there afterwards, holding the value that ended the loop.
#guard outcome [counting .«var» 3.0 (.block []), .exprStmt i] == "3"

-- `for (let i = 0; i < 1; i++) {} i;` — a `let` head is the loop's, and
-- does not leak.
#guard outcome [counting .«let» 1.0 (.block []), .exprStmt i]
  == "uncaught: ReferenceError: i is not defined"

-- `for (let i = i; ;) {}` — and it has a dead zone of its own, so a head
-- that reads itself throws.
#guard outcome
    [.forStmt (some (.decl .«let» [{ target := "i", init := some i }])) none none (.block [])]
  == "uncaught: ReferenceError: Cannot access 'i' before initialization"

-- `let n = 0; for (n = 5; n < 6; n++) {} n;` — an expression head is
-- evaluated for its effect and nothing else.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (num 0.0) }],
      .forStmt (some (.expr (.assign (.ident "n") (num 5.0))))
        (some (.binary .lt (.ident "n") (num 6.0)))
        (some (.update .inc false (.ident "n"))) (.block []),
      .exprStmt (.ident "n") ]
  == "6"

-- `const c = 1; for (const c = 2; c < 3;) { break; } c;` — a `const`
-- head is the loop's too, so the outer binding is untouched.
#guard outcome
    [ .varDecl .«const» [{ target := "c", init := some (num 1.0) }],
      .forStmt (some (.decl .«const» [{ target := "c", init := some (num 2.0) }]))
        (some (.binary .lt (.ident "c") (num 3.0))) none (.block [.breakStmt none]),
      .exprStmt (.ident "c") ]
  == "1"

-- `let n = 0; for (;;) { n++; if (n === 4) break; } n;` — three absent
-- parts, and a `break` is the only exit.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (num 0.0) }],
      .forStmt none none none
        (.block
          [ .exprStmt (.update .inc false (.ident "n")),
            .ifStmt (.binary .strictEq (.ident "n") (num 4.0)) (.breakStmt none) none ]),
      .exprStmt (.ident "n") ]
  == "4"

/-! ## The body, the update, and `continue` -/

-- `let s = 0; for (let i = 0; i < 3; i++) s += i; s;`
#guard outcome
    [ .varDecl .«let» [{ target := "s", init := some (num 0.0) }],
      counting .«let» 3.0 (.exprStmt (.compoundAssign .add (.ident "s") i)),
      .exprStmt (.ident "s") ]
  == "3"

-- `let s = 0; for (let i = 0; i < 3; i++) { if (i === 1) continue; s += i; } s;`
-- — the update still runs for the skipped iteration, so the loop ends.
#guard outcome
    [ .varDecl .«let» [{ target := "s", init := some (num 0.0) }],
      counting .«let» 3.0
        (.block
          [ .ifStmt (.binary .strictEq i (num 1.0)) (.continueStmt none) none,
            .exprStmt (.compoundAssign .add (.ident "s") i) ]),
      .exprStmt (.ident "s") ]
  == "2"

-- `let s = 0; outer: for (let i = 0; i < 3; i++) { for (let j = 0; j < 3; j++)
--    { continue outer; } s += 100; } s;`
-- — a labelled `continue` from the inner loop reaches the *outer* loop's
-- update, and the statement after the inner loop never runs.
#guard outcome
    [ .varDecl .«let» [{ target := "s", init := some (num 0.0) }],
      .labeled "outer"
        (counting .«let» 3.0
          (.block
            [ .forStmt (some (.decl .«let» [{ target := "j", init := some (num 0.0) }]))
                (some (.binary .lt (.ident "j") (num 3.0)))
                (some (.update .inc false (.ident "j")))
                (.block [.continueStmt (some "outer")]),
              .exprStmt (.compoundAssign .add (.ident "s") (num 100.0)) ])),
      .exprStmt (.ident "s") ]
  == "0"

/-! ## The per-iteration binding

CreatePerIterationEnvironment (14.7.4.4). Each iteration gets fresh cells
holding the values the previous iteration ended with, and the update
writes the *new* cells — so the closures the body made see three
different values rather than three views of one. -/

-- `const fs = []; for (let i = 0; i < 3; i++) { fs.push(function () { return i; }); }
--    fs[0]() + "" + fs[2]();`
#guard outcome
    [ .varDecl .«const» [{ target := "fs", init := some (.arrayLit []) }],
      counting .«let» 3.0
        (.block
          [ .exprStmt
              (.call (.member (.ident "fs") "push")
                [.funcExpr none [] [.returnStmt (some i)]]) ]),
      .exprStmt
        (.binary .add
          (.binary .add
            (.call (.index (.ident "fs") (num 0.0)) [])
            (.strLit ""))
          (.call (.index (.ident "fs") (num 2.0)) [])) ]
  == "02"

-- The same body with a `var` head: one cell, so every closure reads the
-- value the loop stopped at.
#guard outcome
    [ .varDecl .«const» [{ target := "fs", init := some (.arrayLit []) }],
      counting .«var» 3.0
        (.block
          [ .exprStmt
              (.call (.member (.ident "fs") "push")
                [.funcExpr none [] [.returnStmt (some i)]]) ]),
      .exprStmt
        (.binary .add
          (.binary .add
            (.call (.index (.ident "fs") (num 0.0)) [])
            (.strLit ""))
          (.call (.index (.ident "fs") (num 2.0)) [])) ]
  == "33"

-- test262's `head-let-fresh-binding-per-iteration.js`, transcribed:
-- `let z = 1, s = 0; for (let x = 1; z < 2; z++) { s += x + z; } s;`
-- — the head binding is copied, so `x` is still 1 on the one iteration.
#guard outcome
    [ .varDecl .«let»
        [ { target := "z", init := some (num 1.0) },
          { target := "s", init := some (num 0.0) } ],
      .forStmt (some (.decl .«let» [{ target := "x", init := some (num 1.0) }]))
        (some (.binary .lt (.ident "z") (num 2.0)))
        (some (.update .inc false (.ident "z")))
        (.block [.exprStmt (.compoundAssign .add (.ident "s")
          (.binary .add (.ident "x") (.ident "z")))]),
      .exprStmt (.ident "s") ]
  == "2"

-- And a body that writes the head binding: the write is carried into the
-- next iteration's cell, which is what makes the copy a copy and not a
-- reset.
#guard outcome
    [ .varDecl .«let» [{ target := "s", init := some (.strLit "") }],
      .forStmt (some (.decl .«let» [{ target := "x", init := some (num 0.0) }]))
        (some (.binary .lt (.ident "x") (num 3.0)))
        (some (.update .inc false (.ident "x")))
        (.block
          [ .exprStmt (.compoundAssign .add (.ident "s") (.ident "x")),
            .exprStmt (.compoundAssign .add (.ident "x") (num 1.0)) ]),
      .exprStmt (.ident "s") ]
  == "02"
