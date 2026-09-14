import Tarski.Simp

/-! A program that calls two `Math` members reduces to its result under
`simp`.

`ArraySimpTest` does this for an Array exotic object and a `NativeFn`;
this is the same shape over what #382 added, and it pins two things at
once. First, **a built-in whose body is a library definition is still
simp-transparent**: `mathUnary` and `toNumberValue` unfold, and the
library's `tsTrunc` and `tsSign` are ordinary definitions `decide` closes,
so each is one local lemma rather than an opaque wall. Second, **a
fifty-three-object `Heap.initial` is still a literal `simp` can push
`readObj` through** — the realm grew by twenty-four objects here, and
nothing needed a size lemma to stay computable.

No prototype step is taken at all: `trunc` and `sign` are own properties
of `Math` rather than inherited ones, and an own-property read is
`getFrom`'s own arm, which is in the set. `ObjectSimpTest` records what
a read that has to climb costs instead. -/

open Tarski

/-- `Math.trunc(2.5) + Math.sign(-3);` -/
private def program : Program :=
  [ .exprStmt (.binary .add
      (.call (.member (.ident "Math") "trunc") [.numLit 2.5])
      (.call (.member (.ident "Math") "sign") [.unary .neg (.numLit 3.0)])) ]

-- The library's operations reduce in the kernel but not under `simp`, so
-- the two values this program reaches are one lemma each, as
-- `ArraySimpTest` carries its `Nat.repr` literals.
@[local simp] private theorem trunc_two_point_five :
    Js.Number.FloatOps.tsTrunc 2.5 = 2.0 := by decide
@[local simp] private theorem sign_neg_three :
    Js.Number.FloatOps.tsSign (-3.0) = -1.0 := by decide
@[local simp] private theorem two_sub_one : (2.0 + -1.0 : Float) = 1.0 := by decide

example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
