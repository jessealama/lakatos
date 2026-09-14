import Tarski.Eval
import Tarski.Format

/-! The temporal dead zone, and the hoisting that produces it.

One mechanism answers three questions. A block's declarations are
instantiated before its first statement runs, so a `let` name is *in
scope* before its declarator is reached — reading it there is a
`ReferenceError`, not `undefined`, which is what distinguishes `let` from
the `var` this slice does not have. The same pre-pass builds every
function declaration in the block, so one may be called above its own
text.

What is pinned here is which programs throw, and with which message: a
dead-zone read names the binding it could not reach, which is a different
refusal from `const`'s. -/

open Tarski

private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-! ## The dead zone -/

-- `x; let x = 1;`
#guard outcome
    [ .exprStmt (.ident "x"),
      .varDecl .«let» [{ target := "x", init := some (.numLit 1.0) }] ]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `let x = 1; x;` — after the declarator, the same name is ordinary.
#guard outcome
    [ .varDecl .«let» [{ target := "x", init := some (.numLit 1.0) }],
      .exprStmt (.ident "x") ]
  == "1"

-- `let x; x;` — a declarator without an initializer ends the dead zone
-- all the same, binding `undefined`.
#guard outcome
    [.varDecl .«let» [{ target := "x", init := none }], .exprStmt (.ident "x")] == "undefined"

-- `x = 1; let x;` — writing into the dead zone throws too, and throws
-- the reference error rather than the const one.
#guard outcome
    [ .exprStmt (.assign (.ident "x") (.numLit 1.0)),
      .varDecl .«let» [{ target := "x", init := none }] ]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `let x = 1; { x; let x = 2; }` — the inner block's own binding shadows
-- the outer one from the block's first statement, so the read is in the
-- *inner* name's dead zone rather than finding the outer 1.
#guard outcome
    [ .varDecl .«let» [{ target := "x", init := some (.numLit 1.0) }],
      .block
        [ .exprStmt (.ident "x"),
          .varDecl .«let» [{ target := "x", init := some (.numLit 2.0) }] ] ]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `const c = 1; c = 2;` — `const` still refuses assignment, and with a
-- TypeError, which is a different refusal from the dead zone's.
#guard outcome
    [ .varDecl .«const» [{ target := "c", init := some (.numLit 1.0) }],
      .exprStmt (.assign (.ident "c") (.numLit 2.0)) ]
  == "uncaught: TypeError: Assignment to constant variable."

/-! ## What hoisting buys -/

-- `function f() { return x; } let x = 2; f();` — a closure may name a
-- binding in its dead zone, as long as it is not called there.
#guard outcome
    [ .funcDecl "f" [] [.returnStmt (some (.ident "x"))],
      .varDecl .«let» [{ target := "x", init := some (.numLit 2.0) }],
      .exprStmt (.call (.ident "f") []) ]
  == "2"

-- `function f() { return x; } f(); let x = 2;` — called there, it throws.
#guard outcome
    [ .funcDecl "f" [] [.returnStmt (some (.ident "x"))],
      .exprStmt (.call (.ident "f") []),
      .varDecl .«let» [{ target := "x", init := some (.numLit 2.0) }] ]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `{ f(); function f() { return 1; } }` — a function declaration is
-- callable above its own text, within its block.
#guard outcome
    [ .block
        [ .exprStmt (.call (.ident "f") []),
          .funcDecl "f" [] [.returnStmt (some (.numLit 1.0))] ] ]
  == "1"

-- `f(); function f() { return 1; }` — and at the top level.
#guard outcome
    [ .exprStmt (.call (.ident "f") []),
      .funcDecl "f" [] [.returnStmt (some (.numLit 1.0))] ]
  == "1"
