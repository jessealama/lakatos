import Tarski.Eval
import Tarski.Format

/-! The `switch` statement.

Three things about it are easy to get wrong and each has a case here.
Selection is strict equality, evaluated clause by clause in source order,
so `"1"` does not select `case 1` and `NaN` selects nothing at all.
Selection picks a *place*, not a clause: everything from there on runs,
`default` included, until a `break` or the clauses run out. And the whole
case block is one declarative scope, instantiated before any test runs,
so a `let` in a later clause is in its dead zone for an earlier one. -/

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

/-- `let r = "";` — the variable the selection cases write. -/
private def declareR : Stmt := .varDecl .«let» [{ target := "r", init := some (.strLit "") }]

/-- `r = <s>;` -/
private def setR (s : String) : Stmt := .exprStmt (.assign (.ident "r") (.strLit s))

/-- `case <n>: r = <s>;` -/
private def caseR (n : Float) (s : String) : SwitchCase :=
  { test := some (num n), body := [setR s] }

/-- Not a number: `0 / 0`, since `NaN` selects nothing and is the point. -/
private def nan : Expr := .binary .div (num 0.0) (num 0.0)

/-! ## Selection and fall-through -/

-- `switch (2) { case 1: r = "a"; case 2: r = "b"; case 3: r = "c"; break;
--    default: r = "d"; } r;`
-- — clause 2 is selected, clause 3 falls through, the `break` stops
-- before `default`.
#guard outcome
    [ declareR,
      .switchStmt (num 2.0)
        [ caseR 1.0 "a",
          caseR 2.0 "b",
          { test := some (num 3.0), body := [setR "c", .breakStmt none] },
          { test := none, body := [setR "d"] } ],
      .exprStmt (.ident "r") ]
  == "c"

-- `switch (9) { case 1: r = "a"; default: r = "d"; case 2: r = "b"; } r;`
-- — nothing matches, so `default` runs and the clause *after* it falls
-- through; the clause before it does not.
#guard outcome
    [ declareR,
      .switchStmt (num 9.0)
        [ caseR 1.0 "a",
          { test := none, body := [setR "d"] },
          caseR 2.0 "b" ],
      .exprStmt (.ident "r") ]
  == "b"

-- `switch (9) { case 1: r = "a"; case 2: r = "b"; } r;` — no match and no
-- `default`: nothing runs.
#guard outcome
    [ declareR,
      .switchStmt (num 9.0) [caseR 1.0 "a", caseR 2.0 "b"],
      .exprStmt (.ident "r") ]
  == ""

-- `switch ("1") { case 1: r = "a"; } r;` — selection is `===`, so a
-- string does not select a number.
#guard outcome
    [ declareR,
      .switchStmt (.strLit "1") [caseR 1.0 "a"],
      .exprStmt (.ident "r") ]
  == ""

-- `switch (0 / 0) { case 0 / 0: r = "a"; } r;` — and NaN selects nothing,
-- itself included.
#guard outcome
    [ declareR,
      .switchStmt nan [{ test := some nan, body := [setR "a"] }],
      .exprStmt (.ident "r") ]
  == ""

-- `switch (2) { case (function () { throw new Error("boom"); })(): ; }` — a
-- test that throws ends the statement where it stands.
#guard outcome
    [ .switchStmt (num 2.0)
        [ { test :=
              some (.call (.funcExpr none []
                [.throwStmt (.new (.ident "Error") [.strLit "boom"])]) []),
            body := [] } ] ]
  == "uncaught: Error: boom"

/-! ## The completion value -/

-- `switch (1) { case 1: 7; break; }` — a `break` carries the running
-- value out.
#guard outcome
    [ .switchStmt (num 1.0)
        [{ test := some (num 1.0), body := [.exprStmt (num 7.0), .breakStmt none] }] ]
  == "7"

-- `switch (1) { case 1: 5; }` — and falling off the end carries it too.
#guard outcome
    [.switchStmt (num 1.0) [{ test := some (num 1.0), body := [.exprStmt (num 5.0)] }]]
  == "5"

-- `2; switch (1) {}` — an empty `switch` completes with `undefined`, not
-- empty, so the 2 does not stand.
#guard outcome [.exprStmt (num 2.0), .switchStmt (num 1.0) []] == "undefined"

/-! ## One scope for the whole case block -/

-- `switch (1) { case 0: let x = 1; case 1: x; }` — the clause that ran
-- never reached the declarator, so `x` is in its dead zone.
#guard outcome
    [ .switchStmt (num 1.0)
        [ { test := some (num 0.0),
            body := [.varDecl .«let» [{ target := "x", init := some (num 1.0) }]] },
          { test := some (num 1.0), body := [.exprStmt (.ident "x")] } ] ]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `switch (0) { case 0: let x = 1; case 1: x = 2; } ` — and once the
-- declarator has run, the later clause writes the same binding.
#guard outcome
    [ .switchStmt (num 0.0)
        [ { test := some (num 0.0),
            body := [.varDecl .«let» [{ target := "x", init := some (num 1.0) }]] },
          { test := some (num 1.0),
            body := [.exprStmt (.assign (.ident "x") (num 2.0))] } ] ]
  == "2"

-- `switch (0) { case 0: f(); function f() { return 7; } }` — a function
-- declaration in a clause is instantiated with the block, so it is
-- callable above its own text.
#guard outcome
    [ .switchStmt (num 0.0)
        [ { test := some (num 0.0),
            body :=
              [ .exprStmt (.call (.ident "f") []),
                .funcDecl "f" [] [.returnStmt (some (num 7.0))] ] } ] ]
  == "7"

/-! ## A `switch` among the jumps -/

-- `let s = 0; for (let i = 0; i < 3; i++) { switch (i) { case 1: continue; }
--    s += 1; } s;`
-- — a `continue` inside a `switch` is not the switch's, so it reaches the
-- loop and skips the statement after it.
#guard outcome
    [ .varDecl .«let» [{ target := "s", init := some (num 0.0) }],
      .forStmt (some (.decl .«let» [{ target := "i", init := some (num 0.0) }]))
        (some (.binary .lt (.ident "i") (num 3.0)))
        (some (.update .inc false (.ident "i")))
        (.block
          [ .switchStmt (.ident "i")
              [{ test := some (num 1.0), body := [.continueStmt none] }],
            .exprStmt (.compoundAssign .add (.ident "s") (num 1.0)) ]),
      .exprStmt (.ident "s") ]
  == "2"

-- `let r = ""; out: switch (1) { case 1: r = "a"; break out; r = "b"; } r;`
-- — a labelled `break` naming the `switch` leaves it, like the unlabelled
-- one, and the rest of the clause does not run.
#guard outcome
    [ declareR,
      .labeled "out"
        (.switchStmt (num 1.0)
          [{ test := some (num 1.0),
             body := [setR "a", .breakStmt (some "out"), setR "b"] }]),
      .exprStmt (.ident "r") ]
  == "a"

-- `let r = ""; out: while (true) { switch (1) { case 1: break out; } r = "b"; } r;`
-- — and one naming the loop around it passes straight through.
#guard outcome
    [ declareR,
      .labeled "out"
        (.whileStmt (.boolLit true)
          (.block
            [ .switchStmt (num 1.0)
                [{ test := some (num 1.0), body := [.breakStmt (some "out")] }],
              setR "b" ])),
      .exprStmt (.ident "r") ]
  == ""
