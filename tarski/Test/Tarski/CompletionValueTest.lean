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
  match runProgram p with
  | none => "<diverges>"
  | some (.error (.throw v)) => s!"uncaught: {formatValue v}"
  | some (.error _) => "<abrupt>"
  | some (.ok none) => "<empty>"
  | some (.ok (some v)) => formatValue v

private def one : Stmt := .exprStmt (.numLit 1.0)
private def yes : Expr := .boolLit true
private def no : Expr := .boolLit false

-- `1;` — the base case the rest are read against.
#guard outcome [one] == "1"

-- `1; let x = 2;` — a declaration completes empty.
#guard outcome [one, .varDecl .«let» [{ name := "x", init := some (.numLit 2.0) }]] == "1"

-- `1; {}` — an empty block completes empty too, so 1 stands.
#guard outcome [one, .block []] == "1"

-- `1; { let x = 5; }` — a block of nothing but declarations, likewise.
#guard outcome [one, .block [.varDecl .«let» [{ name := "x", init := some (.numLit 5.0) }]]] == "1"

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
    [one, .ifStmt yes (.block [.varDecl .«let» [{ name := "x", init := some (.numLit 5.0) }]]) none]
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
     .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
     .whileStmt (.binary .lt (.ident "n") (.numLit 2.0))
       (.block [.exprStmt (.assign "n" (.binary .add (.ident "n") (.numLit 1.0)))])]
  == "2"

/-! ## What ends a run early -/

-- `undeclared;` — an unresolvable reference. The value is a placeholder
-- until #379 allocates a real Error.
#guard outcome [.exprStmt (.ident "undeclared")] == "uncaught: ReferenceError"

-- `const frozen = 1; frozen = 2;` — assignment to an immutable binding.
#guard outcome
    [.varDecl .«const» [{ name := "frozen", init := some (.numLit 1.0) }],
     .exprStmt (.assign "frozen" (.numLit 2.0))]
  == "uncaught: TypeError"

-- `let n = 0; n = 2; n;` — a `let` binding is writable, and the write is
-- visible afterwards because bindings live in the heap.
#guard outcome
    [.varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
     .exprStmt (.assign "n" (.numLit 2.0)),
     .exprStmt (.ident "n")]
  == "2"

-- `{ let n = 1; } n;` — and a block's bindings do not escape it.
#guard outcome
    [.block [.varDecl .«let» [{ name := "n", init := some (.numLit 1.0) }]],
     .exprStmt (.ident "n")]
  == "uncaught: ReferenceError"
