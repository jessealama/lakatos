import Tarski.Eval
import Tarski.Format

/-! `break`, `continue`, and labels — where they go and what value they
carry.

Two things are pinned here, and the second is the easier one to get
wrong. Where a jump goes: an unlabelled `break` ends the innermost loop,
a labelled one ends the statement its label names — which may be a block,
not a loop at all — and a `continue` resumes the loop whose label set
holds its target. What a jump *completes with*: the completion record's
`[[Value]]`, which the spec fills by UpdateEmpty at every statement list
the completion crosses, so `while (true) { 2; break; }` is `2` and not
`undefined`. The evaluator threads a running value through `evalStmt`
instead of catching at every list; the cases below are that threading
measured against what `eval` answers in an engine.

A jump with nowhere to go is an early error in a real engine, and early
errors are outside this epic, so here it escapes as the abrupt completion
it is and the binary exits 1. -/

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
private def n : Expr := .ident "n"

/-- `n = n + k` as a statement. -/
private def bump (name : String) (k : Float) : Stmt :=
  .exprStmt (.assign (.ident name) (.binary .add (.ident name) (num k)))

/-- `let name = x;` -/
private def letNum (name : String) (x : Float) : Stmt :=
  .varDecl .«let» [{ name, init := some (num x) }]

/-! ## Where a jump goes -/

-- `let n = 0; while (true) { n = n + 1; if (n === 3) break; } n;`
#guard outcome
    [ letNum "n" 0.0,
      .whileStmt (.boolLit true)
        (.block
          [ bump "n" 1.0,
            .ifStmt (.binary .strictEq n (num 3.0)) (.breakStmt none) none ]),
      .exprStmt n ]
  == "3"

-- `let n = 0; let s = 0; while (n < 5) { n = n + 1; if (n % 2 === 0) continue; s = s + n; } s;`
-- — the odd numbers below 6, so `continue` really did skip the rest of
-- the body rather than the whole loop.
#guard outcome
    [ letNum "n" 0.0, letNum "s" 0.0,
      .whileStmt (.binary .lt n (num 5.0))
        (.block
          [ bump "n" 1.0,
            .ifStmt (.binary .strictEq (.binary .rem n (num 2.0)) (num 0.0))
              (.continueStmt none) none,
            .exprStmt (.assign (.ident "s") (.binary .add (.ident "s") n)) ]),
      .exprStmt (.ident "s") ]
  == "9"

-- The `labeled-loops` fixture: a labelled `break` out of nested loops.
--
-- ```js
-- let i = 0; let hits = 0;
-- outer: while (i < 3) {
--   i = i + 1;
--   let j = 0;
--   while (j < 3) { j = j + 1; if (j === 2) break outer; hits = hits + 1; }
-- }
-- hits + i * 10;
-- ```
--
-- The inner loop's second iteration leaves both loops at once, so `i` is
-- 1 and `hits` is 1.
#guard outcome
    [ letNum "i" 0.0, letNum "hits" 0.0,
      .labeled "outer"
        (.whileStmt (.binary .lt (.ident "i") (num 3.0))
          (.block
            [ bump "i" 1.0,
              letNum "j" 0.0,
              .whileStmt (.binary .lt (.ident "j") (num 3.0))
                (.block
                  [ bump "j" 1.0,
                    .ifStmt (.binary .strictEq (.ident "j") (num 2.0))
                      (.breakStmt (some "outer")) none,
                    bump "hits" 1.0 ]) ])),
      .exprStmt (.binary .add (.ident "hits") (.binary .mul (.ident "i") (num 10.0))) ]
  == "11"

-- `let i = 0; outer: while (i < 3) { i = i + 1; while (true) { continue outer; } } i;`
-- — a labelled `continue` resumes the outer loop from inside the inner
-- one, which the inner loop must therefore *not* answer for.
#guard outcome
    [ letNum "i" 0.0,
      .labeled "outer"
        (.whileStmt (.binary .lt (.ident "i") (num 3.0))
          (.block
            [ bump "i" 1.0,
              .whileStmt (.boolLit true) (.block [.continueStmt (some "outer")]) ])),
      .exprStmt (.ident "i") ]
  == "3"

-- `a: { 1; break a; 2; }` — a label on a block, which is breakable
-- without being a loop.
#guard outcome
    [ .labeled "a"
        (.block [.exprStmt (num 1.0), .breakStmt (some "a"), .exprStmt (num 2.0)]) ]
  == "1"

-- `a: while (true) { b: { break a; } }` — the inner label refuses a
-- `break` that is not its own and passes it out through the loop.
#guard outcome
    [ .labeled "a"
        (.whileStmt (.boolLit true)
          (.block [.labeled "b" (.block [.breakStmt (some "a")])])) ]
  == "undefined"

-- `let n = 0; while (true) { try { break; } finally { n = n + 1; } } n;`
-- — a `break` out of a `try` runs the finalizer on its way, and the
-- finalizer does not swallow it.
#guard outcome
    [ letNum "n" 0.0,
      .whileStmt (.boolLit true)
        (.block [.tryStmt [.breakStmt none] none (some [bump "n" 1.0])]),
      .exprStmt n ]
  == "1"

/-! ## What a jump completes with

Every expectation here is `eval`'s answer on the same source. -/

-- `1; while (true) { break; }` — the loop's running value starts at
-- `undefined`, and an immediate `break` carries that, not the 1.
#guard outcome [.exprStmt (num 1.0), .whileStmt (.boolLit true) (.block [.breakStmt none])]
  == "undefined"

-- `while (true) { 2; break; }` — a `break` carries what the body had
-- reached.
#guard outcome
    [.whileStmt (.boolLit true) (.block [.exprStmt (num 2.0), .breakStmt none])]
  == "2"

-- `1; while (true) { 2; { break; } }` — and carries it out of the nested
-- list it was in, which is UpdateEmpty.
#guard outcome
    [ .exprStmt (num 1.0),
      .whileStmt (.boolLit true)
        (.block [.exprStmt (num 2.0), .block [.breakStmt none]]) ]
  == "2"

-- `let n = 0; while (n < 2) { n = n + 1; continue; }` — a `continue`
-- carries a value too, and it is the loop's when the loop then ends.
#guard outcome
    [ letNum "n" 0.0,
      .whileStmt (.binary .lt n (num 2.0)) (.block [bump "n" 1.0, .continueStmt none]) ]
  == "2"

-- `let n = 0; while (n < 2) { n = n + 1; 7; continue; }`
#guard outcome
    [ letNum "n" 0.0,
      .whileStmt (.binary .lt n (num 2.0))
        (.block [bump "n" 1.0, .exprStmt (num 7.0), .continueStmt none]) ]
  == "7"

/-! ## A jump with nowhere to go -/

-- `break;` at the top level.
#guard outcome [.breakStmt none] == "<abrupt>"

-- `while (true) { break nope; }` — a label that is not on the stack.
#guard outcome [.whileStmt (.boolLit true) (.block [.breakStmt (some "nope")])] == "<abrupt>"
