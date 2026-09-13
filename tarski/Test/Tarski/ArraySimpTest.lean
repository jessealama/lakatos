import Tarski.Eval

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

`getProp` is unfolded with `rw`, one step per prototype link, for the
reason `ObjectSimpTest` records; through `getProp.eq_def` rather than the
equation theorems, because the string and array arms of its outer match
overlap the catch-all primitive one. `Obj.ownKeys` and `Obj.truncate` are in
the set but never reached: this program calls neither `Object.keys` nor a
`length` write, so a stall on `List.mergeSort` would mean the set had
grown a case the program does not have. -/

open Tarski

/-- `const xs = [1]; xs.push(2); xs.length;` -/
private def program : Program :=
  [ .varDecl .«const» [{ name := "xs", init := some (.arrayLit [.numLit 1.0]) }],
    .exprStmt (.call (.member (.ident "xs") "push") [.numLit 2.0]),
    .exprStmt (.member (.ident "xs") "length") ]

-- `CallSimpTest`'s set plus what an array and a native call add.
attribute [local simp] evalExpr evalExprs evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  callFunction callNative catchReturn makeFunction bindParams pushElements
  newObject newArray newArrayOfLength Obj.array indexProps
  Value.ofNat Obj.truncate Obj.ownKeys Obj.isArray Obj.hasOwn
  NativeFn.constructs setProp
  applyBinary toPrimitive BinaryOp.coerces toNumberPrim toBooleanPrim isStrPrim
  allocCell getCell readCell writeCell initCell
  allocObj readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet
  undefValue thisName DeclKind.isMutable
  Heap.initial globalEnv objectProtoRef arrayProtoRef runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

@[local simp] private theorem repr_zero : Nat.repr 0 = "0" := by decide
@[local simp] private theorem repr_one : Nat.repr 1 = "1" := by decide
@[local simp] private theorem two_toFloat : (2 : Nat).toFloat = 2.0 := by decide

-- `arrayIndex?` is not in the set: unfolding it exposes `String.toList`,
-- and the digit fold under it stalls on an opaque `Nat.toDigits`. The
-- index the program actually parses is one literal, so it is one lemma.
@[local simp] private theorem arrayIndex_one : arrayIndex? "1" = some 1 := by decide

example : runProgram program = some (.ok (some (.prim (.num 2.0)))) := by
  simp [program]
  rw [getProp.eq_def]; simp   -- `xs.push`: not an own property of the instance
  rw [getProp.eq_def]; simp   -- and found on `Array.prototype`
  rw [getProp.eq_def]; simp   -- `xs.length`, answered out of the kind

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 2.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
