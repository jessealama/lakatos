import Tarski.Simp

/-! A program that allocates one object and reads one field reduces to
its result under `simp`.

This is the shape the later correspondence proof needs over objects, as
`Test/Tarski/EvalSimpTest.lean` is over numbers: the recursive equations
are theorems, so `simp` runs the program symbolically — allocating into
the heap's object table, setting a property, resolving the read — until
nothing is left.

A prototype *step* recurses on the *heap* rather than on syntax, so a
plain equation for it would let `simp` unfold it under a binder that
`readObj` has not yet resolved and never stop. `getFromUp` is that step,
and it is in `tarski_eval` as a guarded simproc that fires once per link
a read has to climb — and this read climbs none, because `a` is an own
property of the object the literal built. `getProp` and `getFrom` are
ordinary members: the first dispatches, the second answers an own
property, and neither calls itself.

The literal's object lands at reference 62, just past the realm's
sixty-two intrinsics: a script starts from `Heap.initial`, not from an
empty heap. -/

open Tarski

/-- `const o = { a: 1 }; o.a;` -/
private def program : Program :=
  [ .varDecl .«const» [{ name := "o", init := some (.objectLit [("a", .numLit 1.0)]) }],
    .exprStmt (.member (.ident "o") "a") ]

example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
