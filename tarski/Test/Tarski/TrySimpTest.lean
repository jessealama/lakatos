import Tarski.Simp

/-! A `try`/`finally` whose finalizer overrides reduces to its result
under `simp`.

`Test/Tarski/CallSimpTest.lean` pins that a `return` stays transparent to
`simp` through `catchReturn`; this pins the same for a completion
`attempt` reified and a later step put back. Nothing here is a loop, so
there is no `rw`: the block's completion is caught, matched, and rethrown
inside the fixpoint, and `simp` runs all of it. That is what makes a
postcondition over a function with a `try` in it provable at all.

The program is the issue's own acceptance criterion, `finally` overriding
a `return`, proved rather than only guarded. -/

open Tarski

/-- `function f() { try { return 1; } finally { return 2; } } f();` -/
private def program : Program :=
  [ .funcDecl "f" []
      [.tryStmt [.returnStmt (some (.numLit 1.0))] none
        (some [.returnStmt (some (.numLit 2.0))])],
    .exprStmt (.call (.ident "f") []) ]

-- The realm is eighty-eight objects now, so the term `simp` carries and
-- the kernel then checks is deeper than the default limits admit; see
-- `Test/Tarski/CallSimpTest.lean` and #471.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
example : runProgram program = some (.ok (some (.prim (.num 2.0)))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
