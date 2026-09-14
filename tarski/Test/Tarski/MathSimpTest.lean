import Tarski.Eval

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

-- `ArraySimpTest`'s set plus what a coercing unary built-in adds.
attribute [local simp] evalExpr evalExprs evalStmt evalStmts evalDeclarators
  instantiateBlock hoistNames hoistDeclarators initFunctions
  varNames varNamesStmt varNamesCases hoistVars putIdent applyCoercing
  callFunction callNative catchReturn makeFunction instantiateFunction allocParams initParams hoistVarsFrom
  Param.names hasDefaults expectedArgumentCount Value.ofNat mentionsArguments
  mentionsArgumentsExpr mentionsArgumentsExprs mentionsArgumentsProps
  mentionsArgumentsTarget mentionsArgumentsArrow mentionsArgumentsParams
  mentionsArgumentsClass mentionsArgumentsStmts mentionsArgumentsStmt
  mentionsArgumentsForInit mentionsArgumentsDecls mentionsArgumentsCases pushElements
  newObject newArray newArrayOfLength Obj.array indexProps
  Value.ofNat Obj.truncate Obj.ownKeys Obj.isArray Obj.hasOwn
  NativeFn.constructs getProp setProp getFrom findAccessor
  applyUnary applyBinary toPrimitive BinaryOp.coerces toNumberPrim toBooleanPrim isStrPrim
  toNumberValue mathUnary mathRef
  allocCell getCell readCell writeCell initCell
  allocObj readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj
  Obj.getOwn Obj.setOwn propGet propSet Obj.getOwnAccessor accessorGet
  undefValue thisName DeclKind.isMutable
  Heap.initial globalEnv objectProtoRef arrayProtoRef runScript runProgram evalProgram
  ExceptT.run_bind Except.map throwJsError throwCompletion

-- The library's operations reduce in the kernel but not under `simp`, so
-- the two values this program reaches are one lemma each, as
-- `ArraySimpTest` carries its `Nat.repr` literals.
@[local simp] private theorem trunc_two_point_five :
    Js.Number.FloatOps.tsTrunc 2.5 = 2.0 := by decide
@[local simp] private theorem sign_neg_three :
    Js.Number.FloatOps.tsSign (-3.0) = -1.0 := by decide
@[local simp] private theorem two_sub_one : (2.0 + -1.0 : Float) = 1.0 := by decide

example : runProgram program = some (.ok (some (.prim (.num 1.0)))) := by
  simp [program]

/-- info: some (Except.ok (some (Tarski.Value.prim (Js.JsVal.num 1.000000)))) -/
#guard_msgs in
#eval repr (runProgram program)
