import Tarski.Simp

/-! A template literal reduces to its string under `tarski_eval`.

The companion of `Test/Tarski/ObjectSimpTest.lean` over a template: the
walk is one substitution at a time, ToString after each, and the set
carries `evalTemplate` and the three definitions ToString on a value
bottoms out in.

The substitution is a *string* on purpose. A number would drag
`Number.toDecimalString` into the reduction, and what this file measures
is that the template's own walk is transparent to `simp`, not that the
library's number-to-string is.

`getTemplateObject` is in `tarski_eval` too, but nothing here reaches it:
a tagged template is a call, and a call's reduction is
`Test/Tarski/CallSimpTest.lean`'s shape. -/

open Tarski

/-- `` `a${"x"}b`; `` -/
private def program : Program :=
  [.exprStmt (.template ["a", "b"] [.strLit "x"])]

example : runProgram program = some (.ok (some (.prim (.str "axb")))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.str "axb")))) -/
#guard_msgs in
#eval repr (runProgram program)
