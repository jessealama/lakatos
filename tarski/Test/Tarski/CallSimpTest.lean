import Tarski.Simp

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
  [ .varDecl .«const» [{ target := "f", init := some (.funcExpr none ["x"]
      [.returnStmt (some (.binary .add (.ident "x") (.numLit 1.0)))]) }],
    .exprStmt (.call (.ident "f") [.numLit 2.0]) ]

@[local simp] private theorem two_plus_one : (2.0 + 1.0 : Float) = 3.0 := by decide

-- The realm is eighty-nine objects now, and a function object carries
-- three properties and a `prototype` object of its own, so the term
-- `simp` carries — and the kernel then checks — is deeper than the
-- default limits admit. That whole-program `simp` has a ceiling the
-- heap's representation sets is #471's; raising the limits is the knob
-- until then.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
example : runProgram program = some (.ok (some (.prim (.num 3.0)))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 3.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
