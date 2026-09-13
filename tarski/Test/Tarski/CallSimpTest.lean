import Tarski.Eval

/-! A closed program that calls a function reduces to its result under
`simp`.

What this pins is that a `return` stays transparent: the body ends
abruptly, `catchReturn` turns the completion back into a value, and the
heap the body wrote comes out with it. That is the shape the counter in
`Test/Tarski/FunctionsTest.lean` needs, checked here where the whole
reduction is visible rather than hidden behind `#guard`. -/

open Tarski

/-- `const f = function (x) { return x + 1; }; f(2);` -/
private def program : Program :=
  [ .varDecl .«const» [{ name := "f", init := some (.funcExpr none ["x"]
      [.returnStmt (some (.binary .add (.ident "x") (.numLit 1.0)))]) }],
    .exprStmt (.call (.ident "f") [.numLit 2.0]) ]

-- The simp set of `Test/Tarski/ObjectSimpTest.lean` plus what a call
-- adds. `getProp` is absent for the reason recorded there; this program
-- never reads a property, so it is never needed.
attribute [local simp] evalExpr evalExprs evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  callFunction catchReturn makeFunction bindParams
  applyBinary toPrimitive BinaryOp.coerces toNumberPrim toBooleanPrim isStrPrim
  allocCell getCell readCell writeCell initCell
  allocObj readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet
  undefValue thisName DeclKind.isMutable
  Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

@[local simp] private theorem two_plus_one : (2.0 + 1.0 : Float) = 3.0 := by decide

example : runProgram program = some (.ok (some (.prim (.num 3.0)))) := by
  simp [program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
