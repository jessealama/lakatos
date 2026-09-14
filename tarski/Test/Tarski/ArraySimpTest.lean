import Tarski.Simp

/-! A program that builds an array and calls a built-in on it reduces to
its result under `simp`.

`Test/Tarski/ObjectSimpTest.lean` does this for an object literal and a
property read, and `Test/Tarski/CallSimpTest.lean` for a user function;
this is the same shape over the two things #380 added — an Array exotic
object whose `length` lives in its kind, and a `NativeFn` that
`callNative` interprets. Neither is opaque to `simp`: the index keys, the
`length` arithmetic, and the native's dispatch all compute.

Four literals need lemmas of their own. `Nat.repr`, `Nat.toFloat`, and
the index parse close by `decide` and not by `simp`, so each one the
program reaches is a `@[local simp]` lemma here, as `WhileUnfoldTest`
carries `bump0`.

`getFromUp` and `findPropertyUp` — the prototype *steps* — are taken by
the guarded simprocs `Tarski/Simp.lean` declares, one firing per link
climbed, for the reason `ObjectSimpTest` records. This program climbs
three: `push` is one link up on `Array.prototype`, and the write pays for
the climb too, since `push` goes through `setProp`, which looks for the
first property on the whole chain before writing, so the one element it
stores costs two steps where before the descriptor fold it cost none.
`Obj.ownKeys` is in the set but never reached: this program calls
`Object.keys` nowhere, so a stall on its `List.mergeSort` would mean the
set had grown a case the program does not have. `Obj.truncate` *is*
reached, since `push` is generic over an array-like now and so finishes
with a write to `length` (23.1.3.23 step 5) rather than leaving the kind
to grow on its own; nothing is dropped, so its own sort runs on the empty
list. -/

open Tarski

/-- `const xs = [1]; xs.push(2); xs.length;` -/
private def program : Program :=
  [ .varDecl .«const» [{ target := "xs", init := some (.arrayLit [.numLit 1.0]) }],
    .exprStmt (.call (.member (.ident "xs") "push") [.numLit 2.0]),
    .exprStmt (.member (.ident "xs") "length") ]

@[local simp] private theorem repr_zero : Nat.repr 0 = "0" := by decide
@[local simp] private theorem repr_one : Nat.repr 1 = "1" := by decide
@[local simp] private theorem two_toFloat : (2 : Nat).toFloat = 2.0 := by decide

-- `arrayIndex?` is not in the set: unfolding it exposes `String.toList`,
-- and the digit fold under it stalls on an opaque `Nat.toDigits`. The
-- index the program actually parses is one literal, so it is one lemma.
@[local simp] private theorem arrayIndex_one : arrayIndex? "1" = some 1 := by decide
@[local simp] private theorem arrayIndex_zero : arrayIndex? "0" = some 0 := by decide

-- `push` finishes with a write to `length` (23.1.3.23 step 5), which is
-- ArraySetLength and so a ToUint32; the conversion is over floats and
-- closes by `decide`, one literal like the three above.
@[local simp] private theorem uint32_two : uint32Of? 2.0 = some 2 := by decide

-- The realm is a hundred and eighty-six objects now, so the term
-- `simp` carries through the heap literal is deeper than the default
-- recursion limit admits; `Test/Tarski/TrySimpTest.lean` says the same
-- and #471 is the issue.
set_option maxRecDepth 4000 in
example : runProgram program = some (.ok (some (.prim (.num 2.0)))) := by
  simp [tarski_eval, program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
