import Tarski.Eval
import Tarski.Format

/-! Script completion values, against what a JS engine actually prints.

The binary prints a script's completion value, which is not simply the
last expression's: a declaration completes empty, an empty block leaves
the previous value standing, and `if` and `while` complete with
`undefined` when their body produced nothing. Each case below is written
with the source it models and the value node's `eval` gives it, measured
on the same programs — the rules are subtle enough that the record is
worth more than the derivation. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def one : Stmt := .exprStmt (.numLit 1.0)
private def yes : Expr := .boolLit true
private def no : Expr := .boolLit false

-- `1;` — the base case the rest are read against.
#guard outcome [one] == "1"

-- `1; let x = 2;` — a declaration completes empty.
#guard outcome [one, .varDecl .«let» [{ target := "x", init := some (.numLit 2.0) }]] == "1"

-- `1; {}` — an empty block completes empty too, so 1 stands.
#guard outcome [one, .block []] == "1"

-- `1; { let x = 5; }` — a block of nothing but declarations, likewise.
#guard outcome [one, .block [.varDecl .«let» [{ target := "x", init := some (.numLit 5.0) }]]] == "1"

-- `1; { 2; }` — a block does pass its statements' value through.
#guard outcome [one, .block [.exprStmt (.numLit 2.0)]] == "2"

-- `1; if (false) {}` — `if` completes with undefined, not empty, even
-- when neither arm runs.
#guard outcome [one, .ifStmt no (.block []) none] == "undefined"

-- `1; if (true) {}`
#guard outcome [one, .ifStmt yes (.block []) none] == "undefined"

-- `1; if (true) { let x = 5; }` — an empty body is still undefined here,
-- which is exactly where `if` and a bare block differ.
#guard outcome
    [one, .ifStmt yes (.block [.varDecl .«let» [{ target := "x", init := some (.numLit 5.0) }]]) none]
  == "undefined"

-- `5; if (true) 7; else 8;` — an arm that produces a value gives it.
#guard outcome
    [.exprStmt (.numLit 5.0),
     .ifStmt yes (.exprStmt (.numLit 7.0)) (some (.exprStmt (.numLit 8.0)))]
  == "7"

-- `1; while (false) {}` — the loop's running value starts at undefined.
#guard outcome [one, .whileStmt no (.block [])] == "undefined"

-- `1; let n = 0; while (n < 2) { n = n + 1; }` — and each iteration
-- updates it, so the loop completes with the last body value.
#guard outcome
    [one,
     .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
     .whileStmt (.binary .lt (.ident "n") (.numLit 2.0))
       (.block [.exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))])]
  == "2"

-- `1; ;` — an empty statement completes empty, like a declaration.
#guard outcome [one, .empty] == "1"

-- `if (true) ;` — but `if` still starts from undefined, so an empty
-- statement as its body does not pass 1 through.
#guard outcome [one, .ifStmt yes .empty none] == "undefined"

/-! ## `for` and `switch`

Both are BreakableStatements, so both start from `undefined` rather than
from the enclosing value, and both hand a `break` the value the body had
reached. `for`'s head declaration completes empty, as every declaration
does. -/

/-- `for (let i = 0; i < <n>; i++) <body>` -/
private def counting (n : Float) (body : Stmt) : Stmt :=
  .forStmt (some (.decl .«let» [{ target := "i", init := some (.numLit 0.0) }]))
    (some (.binary .lt (.ident "i") (.numLit n)))
    (some (.update .inc false (.ident "i"))) body

-- `1; for (let i = 0; i < 1; i++) { 3; }` — the body's value.
#guard outcome [one, counting 1.0 (.block [.exprStmt (.numLit 3.0)])] == "3"

-- `1; for (;false;) {}` — a loop whose body never runs still completes
-- with a value.
#guard outcome [one, .forStmt none (some no) none (.block [])] == "undefined"

-- `1; for (let i = 0; i < 2; i++) { 4; break; }` — the `break` carries
-- the value the body had reached.
#guard outcome
    [one, counting 2.0 (.block [.exprStmt (.numLit 4.0), .breakStmt none])]
  == "4"

-- `1; for (let i = 0; i < 2; i++) { if (i === 1) break; 4; }` — but a
-- `break` inside an `if` does not, because `if` fills its arm's empty
-- completion value with `undefined` before anything else sees it
-- (14.6.2 step 4). Measured against `eval` in V8, which agrees.
#guard outcome
    [one,
     counting 2.0
       (.block
         [.ifStmt (.binary .strictEq (.ident "i") (.numLit 1.0)) (.breakStmt none) none,
          .exprStmt (.numLit 4.0)])]
  == "undefined"

-- `1; switch (1) { case 1: 5; }`
#guard outcome
    [one, .switchStmt (.numLit 1.0)
      [{ test := some (.numLit 1.0), body := [.exprStmt (.numLit 5.0)] }]]
  == "5"

-- `2; switch (1) {}` — and an empty one completes with undefined.
#guard outcome [.exprStmt (.numLit 2.0), .switchStmt (.numLit 1.0) []] == "undefined"

/-! ## What ends a run early -/

-- `undeclared;` — an unresolvable reference.
#guard outcome [.exprStmt (.ident "undeclared")] == "uncaught: ReferenceError: undeclared is not defined"

-- `const frozen = 1; frozen = 2;` — assignment to an immutable binding.
#guard outcome
    [.varDecl .«const» [{ target := "frozen", init := some (.numLit 1.0) }],
     .exprStmt (.assign (.ident "frozen") (.numLit 2.0))]
  == "uncaught: TypeError: Assignment to constant variable."

-- `let n = 0; n = 2; n;` — a `let` binding is writable, and the write is
-- visible afterwards because bindings live in the heap.
#guard outcome
    [.varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
     .exprStmt (.assign (.ident "n") (.numLit 2.0)),
     .exprStmt (.ident "n")]
  == "2"

-- `{ let n = 1; } n;` — and a block's bindings do not escape it.
#guard outcome
    [.block [.varDecl .«let» [{ target := "n", init := some (.numLit 1.0) }]],
     .exprStmt (.ident "n")]
  == "uncaught: ReferenceError: n is not defined"
