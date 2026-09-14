import Tarski.Eval

/-! A postcondition proved through a `for`, one iteration at a time.

`Test/Tarski/WhileUnfoldTest.lean` is the same shape over a `while`.
`evalFor` is the second definition whose equation never joins a simp set,
and for the same reason: added to one it would rewrite forever on a loop
whose exit simp cannot see, while `rw` exposes exactly one iteration. So
the `rw` count is the iteration count here too.

What this test pins beyond that is that the machinery around the loop
stays transparent to `simp`: the `var` pass (`varNames`, `hoistVars`)
that now runs ahead of every script, the per-iteration copy
(`copyBindings`, `Env.rebind`), the head's own scope, and the update
operator. If any of those became opaque, a `@ensures` proof over a
counted loop would stop reducing, and this is where that shows up. -/

open Tarski

/-- `let s = 0; for (let i = 0; i < 2; i++) { s = s + i; } s;` -/
private def program : Program :=
  [ .varDecl .«let» [{ name := "s", init := some (.numLit 0.0) }],
    .forStmt (some (.decl .«let» [{ name := "i", init := some (.numLit 0.0) }]))
      (some (.binary .lt (.ident "i") (.numLit 2.0)))
      (some (.update .inc false (.ident "i")))
      (.block [.exprStmt (.assign (.ident "s") (.binary .add (.ident "s") (.ident "i")))]),
    .exprStmt (.ident "s") ]

-- `Test/Tarski/WhileUnfoldTest.lean`'s set plus what a `for` adds: the
-- `var` pass every script now runs, the head's scope and its copies, and
-- the update operator. `evalForLoop` is in it and `evalFor` is not —
-- the first runs once, the second is the loop.
attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  evalForLoop copyBindings Env.rebind UpdateOp.step
  allocCell getCell readCell writeCell initCell putIdent
  Env.lookup Heap.alloc Heap.read Heap.write
  applyBinary applyUnary applyStrict BinaryOp.coerces applyCoercing toPrimitive
  toNumberPrim toBooleanPrim isStrPrim toStringPrim strictEqValue
  evalBlock evalLoop attempt liftCompletion loopContinues
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- What each iteration's counter bump and running sum leave behind.
@[local simp] private theorem bump0 : (0.0 + 1.0 : Float) = 1.0 := by decide
@[local simp] private theorem bump1 : (1.0 + 1.0 : Float) = 2.0 := by decide
@[local simp] private theorem sum0 : (0.0 + 0.0 : Float) = 0.0 := by decide
@[local simp] private theorem sum1 : (0.0 + 1.0 : Float) = 1.0 := by decide

/-- The loop runs twice and leaves `s` at 1, which is the script's
completion value. -/
example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp +decide [program]
  rw [evalFor]; simp +decide  -- i = 0, test true: s becomes 0, i becomes 1
  rw [evalFor]; simp +decide  -- i = 1, test true: s becomes 1, i becomes 2
  rw [evalFor]; simp +decide  -- i = 2, test false: the loop exits

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
