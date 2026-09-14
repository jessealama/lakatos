import Tarski.Eval

/-! A postcondition proved through a `do`/`while`, one iteration at a
time — `Test/Tarski/WhileUnfoldTest.lean`'s twin.

`evalDoWhile` is `evalWhile`'s neighbour on the short list of definitions
whose equations never join a simp set: it recurses until a heap value
says stop, which `simp` cannot see, so it is unfolded with `rw`. Its
equation is a different one from `evalWhile`'s — the body comes first —
which is why the two are separate definitions rather than one with a
flag, and it is what makes the count below three rather than four: the
last unfolding is the one whose test fails, and the body has already run
that many times. -/

open Tarski

/-- `let n = 0; do { n = n + 1; } while (n < 3); n;` -/
private def program : Program :=
  [ .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
    .doWhileStmt
      (.block [.exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))])
      (.binary .lt (.ident "n") (.numLit 3.0)),
    .exprStmt (.ident "n") ]

attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators evalNamed
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  allocCell getCell readCell writeCell initCell putIdent
  Env.lookup Heap.alloc Heap.read Heap.write
  applyBinary applyUnary applyStrict BinaryOp.coerces applyCoercing toPrimitive
  toNumberPrim toBooleanPrim isStrPrim toStringPrim strictEqValue
  evalBlock evalDoLoop attempt liftCompletion loopContinues
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- What each iteration's counter bump leaves behind; the test itself is
-- `decide (a < b)` over the library's binary64 order, which `+decide`
-- settles.
@[local simp] private theorem bump0 : (0.0 + 1.0 : Float) = 1.0 := by decide
@[local simp] private theorem bump1 : (1.0 + 1.0 : Float) = 2.0 := by decide
@[local simp] private theorem bump2 : (2.0 + 1.0 : Float) = 3.0 := by decide

/-- The body runs three times and leaves `n` at 3, which is the script's
completion value. -/
example : runProgram program = some (.ok (some (.prim (.num 3.0)))) := by
  simp +decide [program]
  rw [evalDoWhile]; simp +decide  -- body: n becomes 1; test true
  rw [evalDoWhile]; simp +decide  -- body: n becomes 2; test true
  rw [evalDoWhile]; simp +decide  -- body: n becomes 3; test false, the loop exits

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
