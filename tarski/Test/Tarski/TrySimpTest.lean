import Tarski.Eval

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

-- `Test/Tarski/CallSimpTest.lean`'s set plus what a `try` adds:
-- `attempt`, which reifies the block's completion, and
-- `liftCompletion`, which puts it back.
attribute [local simp] evalExpr evalExprs evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars
  callFunction catchReturn makeFunction instantiateFunction allocParams initParams hoistVarsFrom
  Param.names hasDefaults expectedArgumentCount Value.ofNat mentionsArguments
  mentionsArgumentsExpr mentionsArgumentsExprs mentionsArgumentsProps
  mentionsArgumentsTarget mentionsArgumentsArrow mentionsArgumentsParams
  mentionsArgumentsClass mentionsArgumentsStmts mentionsArgumentsStmt
  mentionsArgumentsForInit mentionsArgumentsDecls mentionsArgumentsCases
  evalBlock attempt liftCompletion
  applyBinary toPrimitive BinaryOp.coerces applyCoercing toNumberPrim toBooleanPrim isStrPrim
  allocCell getCell readCell writeCell initCell putIdent
  allocObj newObject readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet
  undefValue thisName DeclKind.isMutable
  Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

example : runProgram program = some (.ok (some (.prim (.num 2.0)))) := by
  simp [program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
