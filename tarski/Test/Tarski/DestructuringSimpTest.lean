import Tarski.Simp

/-! A closed destructuring reduces to its result under `simp`.

This is `Test/Tarski/ObjectSimpTest.lean`'s shape over the two pattern
families, and the array half is the proof that splitting
`callIteratorNative` out of `callNative` cost nothing: unlike
`callReflectNative`, `callSymbolNative`, and `callJsonNative`, it **is**
in `tarski_eval`, so the array's own `@@iterator`,
`%ArrayIteratorPrototype%`'s `next`, and the iterator result object all
unfold in the set. What has to reduce for the first example to close:
GetIterator through the realm's `Array.prototype[@@iterator]`, one
`arrayIteratorNext`, and the write of the leaf.

**One element is the ceiling, and the ceiling is #471's.** Measured on
this branch with `maxHeartbeats 4000000` and `maxRecDepth 8000`: the
one-element array pattern below elaborates and passes the kernel in about
thirteen seconds, against `ObjectSimpTest`'s one and a half; a *second*
element — two steps and the step that finds the array done — runs past
six minutes with no answer, and the issue's own
`const [a, b = 5] = [1]; const { c } = { c: 2 }; a + b + c` elaborates in
fifty seconds and then times out in the kernel. The ceiling is the heap's
representation rather than the protocol, which is the same finding
`tarski/CLAUDE.md` records for `Gate`, so the larger programs are pinned
by `#eval` here and by `Test/Tarski/DestructuringTest.lean` in full.

Four literals need lemmas of their own, as `Test/Tarski/ArraySimpTest.lean`
carries its index parse: `Nat.repr`, `Nat.toFloat`, the index parse, and
ToLength's integer part each close by `decide` and not by `simp`. -/

open Tarski

/-- `const [a] = [1]; a;` -/
private def fromArray : Program :=
  [ .varDecl .«const»
      [ { target := .array [some { target := "a", default := none }] none,
          init := some (.arrayLit [.numLit 1.0]) } ],
    .exprStmt (.ident "a") ]

/-- `const { c } = { c: 2 }; c;` -/
private def fromObject : Program :=
  [ .varDecl .«const»
      [ { target := .object [{ key := .name "c", target := "c", default := none }] none,
          init := some (.objectLit [.init "c" (.numLit 2.0)]) } ],
    .exprStmt (.ident "c") ]

/-- The issue's own pair, which only `#eval` reaches. -/
private def issueExample : Program :=
  [ .varDecl .«const»
      [ { target := .array
            [ some { target := "a", default := none },
              some { target := "b", default := some (.numLit 5.0) } ] none,
          init := some (.arrayLit [.numLit 1.0]) } ],
    .varDecl .«const»
      [ { target := .object [{ key := .name "c", target := "c", default := none }] none,
          init := some (.objectLit [.init "c" (.numLit 2.0)]) } ],
    .exprStmt (.binary .add (.binary .add (.ident "a") (.ident "b")) (.ident "c")) ]

@[local simp] private theorem repr_zero : Nat.repr 0 = "0" := by decide
@[local simp] private theorem arrayIndex_zero : arrayIndex? "0" = some 0 := by decide
@[local simp] private theorem one_toFloat : (1 : Nat).toFloat = 1.0 := by decide
@[local simp] private theorem len_one :
    Js.Number.FloatOps.integerOrInfinity? 1.0 = some 1 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
example : runProgram fromArray = some (.ok (some (.prim (.num 1.0)))) := by
  simp [tarski_eval, fromArray]

set_option maxRecDepth 8000 in
example : runProgram fromObject = some (.ok (some (.prim (.num 2.0)))) := by
  simp [tarski_eval, fromObject]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram fromArray)

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram fromObject)

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 8.000000)))) -/
#guard_msgs in
#eval repr (runProgram issueExample)
