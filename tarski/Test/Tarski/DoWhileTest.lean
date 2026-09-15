import Tarski.Eval
import Tarski.Format

/-! The `do`/`while` statement.

It differs from `while` in one place and it is the one every case here
is about: the body runs before the first test, so it always runs at
least once. Everything else it shares — it is a BreakableStatement, a
`continue` it answers for goes to the *test* rather than out, a labelled
`continue` naming it is its own, and a `var` inside it belongs to the
function around it. -/

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

/-- `let <n> = <x>;` -/
private def declare (n : String) (x : Float) : Stmt :=
  .varDecl .«let» [{ target := n, init := some (num x) }]

/-- `<n>++;` -/
private def bump (n : String) : Stmt := .exprStmt (.update .inc false (.ident n))

/-! ## The body runs before the test -/

-- `let i = 0; do { i++; } while (i < 3); i;`
#guard outcome
    [ declare "i" 0.0,
      .doWhileStmt (.block [bump "i"]) (.binary .lt (.ident "i") (num 3.0)),
      .exprStmt (.ident "i") ]
  == "3"

-- `let r = 0; do { r = 1; } while (false); r;` — the whole difference
-- from `while`, which would leave `r` at 0.
#guard outcome
    [ declare "r" 0.0,
      .doWhileStmt (.block [.exprStmt (.assign (.ident "r") (num 1.0))]) (.boolLit false),
      .exprStmt (.ident "r") ]
  == "1"

/-! ## Completion values -/

-- `do { 7; } while (false);`
#guard outcome [.doWhileStmt (.block [.exprStmt (num 7.0)]) (.boolLit false)] == "7"

-- `do ; while (false);` — the empty statement completes empty, so the
-- loop's own starting value stands.
#guard outcome [.doWhileStmt .empty (.boolLit false)] == "undefined"

-- `do { 5; break; } while (true);` — a `break` carries the running
-- value out, and it is the loop that answers with it.
#guard outcome
    [.doWhileStmt (.block [.exprStmt (num 5.0), .breakStmt none]) (.boolLit true)]
  == "5"

/-! ## `continue` reaches the test -/

-- `let i = 0; let hits = 0; do { i++; if (i % 2) continue; hits++; } while (i < 4); hits;`
-- — the `continue` skips the rest of the body and goes to the test, so
-- the loop still ends; `hits` counts the even steps.
#guard outcome
    [ declare "i" 0.0,
      declare "hits" 0.0,
      .doWhileStmt
        (.block
          [ bump "i",
            .ifStmt (.binary .rem (.ident "i") (num 2.0)) (.continueStmt none) none,
            bump "hits" ])
        (.binary .lt (.ident "i") (num 4.0)),
      .exprStmt (.ident "hits") ]
  == "2"

/-! ## Labels -/

-- `let r = ""; outer: for (let i = 0; i < 3; i++) { let j = 0;
--    do { j++; if (i === 1) continue outer; r = r + i; } while (j < 2); }
--  r;`
-- — the labelled `continue` is the *outer* loop's, so it leaves the
-- `do`/`while` entirely and the `i === 1` pass contributes nothing.
#guard outcome
    [ .varDecl .«let» [{ target := "r", init := some (.strLit "") }],
      .labeled "outer"
        (.forStmt (some (.decl .«let» [{ target := "i", init := some (num 0.0) }]))
          (some (.binary .lt (.ident "i") (num 3.0)))
          (some (.update .inc false (.ident "i")))
          (.block
            [ declare "j" 0.0,
              .doWhileStmt
                (.block
                  [ bump "j",
                    .ifStmt (.binary .strictEq (.ident "i") (num 1.0))
                      (.continueStmt (some "outer")) none,
                    .exprStmt (.assign (.ident "r")
                      (.binary .add (.ident "r") (.ident "i"))) ])
                (.binary .lt (.ident "j") (num 2.0)) ])),
      .exprStmt (.ident "r") ]
  == "0022"

-- `let i = 0; inner: do { i++; break inner; } while (true); i;` — a
-- labelled `break` naming the loop is caught by the label, not by the
-- loop, and either way the loop ends.
#guard outcome
    [ declare "i" 0.0,
      .labeled "inner"
        (.doWhileStmt (.block [bump "i", .breakStmt (some "inner")]) (.boolLit true)),
      .exprStmt (.ident "i") ]
  == "1"

-- `let i = 0; outer: do { i++; continue outer; } while (i < 2); i;` — a
-- labelled `continue` naming the `do`/`while` itself is *its* continue,
-- so it reaches the test like an unlabelled one.
#guard outcome
    [ declare "i" 0.0,
      .labeled "outer"
        (.doWhileStmt (.block [bump "i", .continueStmt (some "outer")])
          (.binary .lt (.ident "i") (num 2.0))),
      .exprStmt (.ident "i") ]
  == "2"

/-! ## Hoisting descends into it -/

-- `do { var v = 1; } while (false); v;` — a `var` inside the body is
-- the script's, so `varNames` must walk through this statement too.
#guard outcome
    [ .doWhileStmt
        (.block [.varDecl .«var» [{ target := "v", init := some (num 1.0) }]])
        (.boolLit false),
      .exprStmt (.ident "v") ]
  == "1"
