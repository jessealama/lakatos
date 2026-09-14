import Tarski.Eval

/-! A postcondition proved through a `while`, one iteration at a time.

`evalWhile` is the one definition whose equation never joins a simp set.
Added to one, it would rewrite forever on a loop whose exit simp cannot
see; used with `rw`, it exposes exactly one iteration, and the proof is
the loop run symbolically: unfold, simplify, unfold, until the test is
false. The `rw` count is therefore the iteration count, and a loop whose
bound is not a literal needs an invariant instead — which is the shape
the epic's `@ensures` proofs will take. -/

open Tarski

/-- `let n = 0; while (n < 3) { n = n + 1; } n;` -/
private def program : Program :=
  [ .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
    .whileStmt (.binary .lt (.ident "n") (.numLit 3.0))
      (.block [.exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))]),
    .exprStmt (.ident "n") ]

attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  allocCell getCell readCell writeCell initCell putIdent
  Env.lookup Heap.alloc Heap.read Heap.write
  applyBinary applyUnary applyStrict BinaryOp.coerces applyCoercing toPrimitive
  toNumberPrim toBooleanPrim isStrPrim toStringPrim strictEqValue
  evalBlock evalLoop attempt liftCompletion loopContinues
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- What each iteration's counter bump leaves behind. `simp +decide`
-- settles the loop test itself, which is `decide (a < b)` over the
-- library's binary64 order and so a decidable proposition.
@[local simp] private theorem bump0 : (0.0 + 1.0 : Float) = 1.0 := by decide
@[local simp] private theorem bump1 : (1.0 + 1.0 : Float) = 2.0 := by decide
@[local simp] private theorem bump2 : (2.0 + 1.0 : Float) = 3.0 := by decide

/-- The loop runs three times and leaves `n` at 3, which is the script's
completion value. -/
example : runProgram program = some (.ok (some (.prim (.num 3.0)))) := by
  simp +decide [program]
  rw [evalWhile]; simp +decide  -- n = 0, test true: n becomes 1
  rw [evalWhile]; simp +decide  -- n = 1, test true: n becomes 2
  rw [evalWhile]; simp +decide  -- n = 2, test true: n becomes 3
  rw [evalWhile]; simp +decide  -- n = 3, test false: the loop exits

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
