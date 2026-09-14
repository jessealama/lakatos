import Tarski.Simp

/-! A labelled `break` out of nested loops, proved one iteration at a
time.

`Test/Tarski/WhileUnfoldTest.lean` is the same shape over one loop and a
normal exit; this one adds the part a catching arm could break. The
`break outer` is thrown from the inner loop's body, crosses two
`attempt`s — the inner `evalWhile`'s and the inner `evalLoop`'s, neither
of which answers for it — and is caught by `evalLabeled`'s frame for
`outer`. That all of it stays transparent to `simp` is what makes a
postcondition over a loop with a labelled exit provable at all, and the
`rw` count is still the iteration count: one outer, one inner. -/

open Tarski

/-- `let n = 0; outer: while (true) { n = n + 1; while (true) { break outer; } } n;` -/
private def program : Program :=
  [ .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
    .labeled "outer"
      (.whileStmt (.boolLit true)
        (.block
          [ .exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0))),
            .whileStmt (.boolLit true) (.block [.breakStmt (some "outer")]) ])),
    .exprStmt (.ident "n") ]

-- `Test/Tarski/WhileUnfoldTest.lean`'s set plus what a label and a
-- caught completion add. `attempt` is in it and `evalWhile` is not: the
-- first is an ordinary definition whose unfolding terminates, the second
-- is the loop.
-- `applyCoercing_prim` and `toNumberValue_prim` (`Tarski/Simp.lean`) are
-- the two ground lemmas that close a coercion of a primitive in one
-- rewrite: ToPrimitive answers a `Value` now, so without them every
-- iteration's arithmetic pushes `simp` through a constructor match.
attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators evalNamed
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  allocCell getCell readCell writeCell initCell putIdent
  Env.lookup Heap.alloc Heap.read Heap.write
  applyBinary applyUnary applyStrict BinaryOp.coerces applyCoercing toPrimitive toNumberValue applyCoercing_prim toNumberValue_prim
  toNumberPrim toBooleanPrim isStrPrim toStringPrim strictEqValue
  evalBlock evalLabeled evalLoop attempt liftCompletion loopContinues
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

@[local simp] private theorem bump0 : (0.0 + 1.0 : Float) = 1.0 := by decide

/-- The inner loop's first iteration leaves both loops, so `n` is 1. -/
example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp +decide [program]
  rw [evalWhile]; simp +decide  -- the outer loop's first iteration
  rw [evalWhile]; simp +decide  -- the inner loop's, which breaks out of both

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
