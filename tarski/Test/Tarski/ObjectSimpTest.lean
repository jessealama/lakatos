import Tarski.Eval

/-! A program that allocates one object and reads one field reduces to
its result under `simp`.

This is the shape the later correspondence proof needs over objects, as
`Test/Tarski/EvalSimpTest.lean` is over numbers: the recursive equations
are theorems, so `simp` runs the program symbolically — allocating into
the heap's object table, setting a property, resolving the read — until
nothing is left.

`getProp` is the second definition, after `evalWhile`, whose equation
never joins a simp set, and for the same reason: its recursion is on the
*heap* rather than on syntax, so `simp` unfolds it under the binder that
`readObj` has not yet resolved and never stops. Both are unfolded one
step at a time with `rw`, and the `rw` count is the step count — here one
prototype link, which finds the property it is looking for.

The literal's object lands at reference 15, just past the realm's fifteen
intrinsics: a script starts from `Heap.initial`, not from an empty
heap. -/

open Tarski

/-- `const o = { a: 1 }; o.a;` -/
private def program : Program :=
  [ .varDecl .«const» [{ name := "o", init := some (.objectLit [("a", .numLit 1.0)]) }],
    .exprStmt (.member (.ident "o") "a") ]

-- The simp set: the evaluator's non-loop equations, the state helpers
-- they bottom out in, and the object operations this program performs.
-- `ExceptT.run_bind` and `Except.map` are the plumbing core does not tag
-- (see `Tarski/Monad.lean`); the rest is the evaluator's own.
attribute [local simp] evalExpr evalStmt evalStmts evalDeclarators evalProps
  instantiateBlock hoistNames hoistDeclarators initFunctions
  setProp
  allocCell getCell readCell writeCell initCell
  allocObj readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet
  DeclKind.isMutable Heap.initial globalEnv runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp [program]
  rw [getProp]; simp  -- the read: one link, an own property

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
