import Tarski.Eval

/-! A closed, loop-free program reduces to its result under `simp`.

This is the shape every `@ensures` proof over the evaluator will take:
the recursive equations are theorems, so `simp` runs the program
symbolically until nothing is left but binary64 arithmetic, and the
arithmetic is closed by `decide` against the library's own definitions.
Nothing here is an unfolding of `evalWhile` — that one is `rw`'s, and
`Test/Tarski/WhileUnfoldTest.lean` is where it happens.

`decide` cannot do this job on its own: a `partial_fixpoint` definition
has equations, not a reduction behaviour, so the kernel does not compute
it. The `#eval` below is the other half — the compiled evaluator agrees
with the proved one. -/

open Tarski

/-- `let x = 3; const y = x * 2.5; y === 7.5 ? 1 : 0` -/
private def program : Program :=
  [ .varDecl .«let» [{ name := "x", init := some (.numLit 3.0) }],
    .varDecl .«const» [{ name := "y", init := some (.binary .mul (.ident "x") (.numLit 2.5)) }],
    .exprStmt (.cond (.binary .strictEq (.ident "y") (.numLit 7.5))
      (.numLit 1.0) (.numLit 0.0)) ]

-- The simp set: the evaluator's equations other than `evalWhile`'s and
-- `getProp`'s, the block instantiation and state helpers they bottom out
-- in, and the two binary64 facts left over once the program has run.
-- `ExceptT.run_bind` and `Except.map` are the transformer plumbing core
-- does not tag as `simp`; `Tarski/Monad.lean` says why. `Js.JsVal.strictEq`
-- is the library's `===`; the evaluator only dispatches to it.
attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  allocCell getCell readCell writeCell initCell putIdent
  Env.lookup Heap.alloc Heap.read Heap.write
  applyBinary applyUnary applyStrict BinaryOp.coerces applyCoercing toPrimitive
  toNumberPrim toBooleanPrim isStrPrim toStringPrim strictEqValue
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram Js.JsVal.strictEq
  ExceptT.run_bind Except.map throwJsError throwCompletion

@[local simp] private theorem three_times_two_and_a_half : (3.0 * 2.5 : Float) = 7.5 := by decide
@[local simp] private theorem seven_and_a_half_self : ((7.5 : Float) == 7.5) = true := by decide

example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp [program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
