import Tarski.Eval
import Tarski.SimpAttr

/-! `tarski_eval`: the evaluator's partial-evaluation set.

A proof about a closed, loop-free program is `simp [tarski_eval]` and
nothing else. Before this module every such proof carried its own
`attribute [local simp]` list — seven of them under `Test/Tarski/`, each
a superset of the last — and a correspondence obligation stated outside
this package could not have one at all. The set is the list, kept once.

**What decides membership.** A definition that recurses on *syntax* runs
out, so it is an ordinary member: `evalExpr` and its neighbours descend a
concrete AST. A definition that recurses on a *loop* never stops, so it
is never in the set at all and is unfolded one step at a time with `rw`:
`evalWhile`, `evalDoWhile`, `evalFor`, and `joinElements`, whose tests are
the `*UnfoldTest` files. A definition that recurses on the *heap* is in
between: it stops as soon as the heap says so, but `simp` will unfold it
forever under a reference it has not yet resolved. Those four —
`getFromUp`, `findAccessorUp`, `protoChainHas`, and `construct` — join
the set as *guarded simprocs* below, which fire only when the reference
they are handed is a literal. A concrete heap has resolved it by then,
which is exactly when the hand-written `rw` used to be legal.

**The two cycles.** `construct` is not recursive in itself; it calls
`callFunction` in its ordinary-constructor arm, and `callFunction` used
to call it back for an `Error` constructor called without `new`, so a
simp set holding both descended through the pair forever — and no guard
could stop it, because both arms pass the *same literal* object. That arm
is now written out in `Tarski/Eval.lean` (it is what `construct`'s own
errorCtor arm does), so the cycle is gone and the guard is enough. The
other cycle, `construct` ↔ `constructClass` through a derived implicit
constructor, passes a *bound* parent reference, so the guard does stop
it, exactly as it stops `getFromUp` and the other two prototype walks.

**`Heap.initial` stays in the set.** Folding the realm behind per-
reference read lemmas was measured while planning #479 and did not lift
the kernel ceiling #471 records; it made elaboration slower instead. A
fifty-nine-object literal heap is something `simp` pushes `readObj`
through. -/

namespace Tarski

open Js

/-! ## The equations

One block, grouped the way the tests' lists were. Every name here
recurses on syntax or not at all. -/

-- Evaluation proper, and the instantiation a block is preceded by.
attribute [tarski_eval]
  evalExpr evalExprs evalStmt evalStmts evalProps evalDeclarators evalBlock
  instantiateBlock hoistNames hoistDeclarators initFunctions

-- `var` hoisting: VarDeclaredNames over a body, and the cells it gives them.
attribute [tarski_eval]
  varNames varNamesStmt varNamesCases hoistVars

-- Calls: user code, built-ins, and the two opaque catch sites.
attribute [tarski_eval]
  callFunction callNative constructNative catchReturn attempt liftCompletion
  makeFunction isConstructor NativeFn.constructs
  toStringValue toNumberValue toNumberValues mathUnary pushElements

-- FunctionDeclarationInstantiation: parameters, their defaults, the
-- `var`s a body hoists past them, and the `arguments` object a body that
-- mentions the name is given. `mentionsArguments` is a syntactic scan.
attribute [tarski_eval]
  instantiateFunction allocParams initParams hoistVarsFrom
  Param.names hasDefaults expectedArgumentCount
  makeArguments argumentsName mentionsArguments
  mentionsArgumentsExpr mentionsArgumentsExprs mentionsArgumentsProps
  mentionsArgumentsTarget mentionsArgumentsArrow mentionsArgumentsParams
  mentionsArgumentsClass mentionsArgumentsStmts mentionsArgumentsStmt
  mentionsArgumentsForInit mentionsArgumentsDecls mentionsArgumentsCases

-- Classes and private elements.
attribute [tarski_eval]
  evalClass defineMethods initializeInstance initFields initFieldList
  constructClass runConstructor bindPrivateNames privateName
  readPrivate writePrivate addPrivate allocFromConstructor
  ClassDef.constructor? ClassDef.instanceFields ClassDef.staticFields
  ClassDef.privateNames classFields dedupNames firstConstructor privateFieldNames

-- Property reads and writes, own-property depth only: the two prototype
-- steps are guarded simprocs below.
attribute [tarski_eval]
  getProp setProp getFrom findAccessor

-- The `Obj` operations and the lists they keep.
attribute [tarski_eval]
  Obj.getOwn Obj.setOwn Obj.getOwnAccessor Obj.getPrivate Obj.setPrivate Obj.addPrivate
  Obj.defineData Obj.defineAccessor Obj.isArray Obj.hasOwn Obj.ownKeys Obj.truncate
  Obj.array indexProps
  propGet propSet propDrop accessorGet accessorSet accessorDrop privateGet privateSet

-- Operators and coercions. Every primitive operation is the library's;
-- the evaluator only dispatches onto it.
attribute [tarski_eval]
  applyBinary applyUnary applyStrict applyCoercing BinaryOp.coerces
  toPrimitive toNumberPrim toBooleanPrim toStringPrim isStrPrim
  strictEqValue sameValueValue Js.JsVal.strictEq Value.ofNat

-- Cells, objects, and the heap underneath both.
attribute [tarski_eval]
  allocCell getCell readCell writeCell initCell putIdent
  allocObj newObject newArray newArrayOfLength readObj writeObj modifyObj
  Env.lookup Heap.alloc Heap.read Heap.write
  Heap.allocObj Heap.readObj Heap.writeObj

-- The evaluator's own reserved names and the one flag on a declaration form.
attribute [tarski_eval]
  undefValue thisName homeName newTargetName activeFunctionName DeclKind.isMutable

-- The realm: the initial heap, the global scope chain, and every
-- intrinsic's reference, so a read that lands on one computes.
attribute [tarski_eval]
  Heap.initial globalEnv
  ErrorKind.protoRef ErrorKind.ctorRef ErrorKind.cellRef ErrorKind.name ErrorKind.all
  errorToStringRef objectProtoRef objectCtorRef objectHasOwnPropertyRef objectIsRef
  objectKeysRef arrayProtoRef arrayCtorRef arrayPushRef arrayJoinRef arrayIsArrayRef
  stringCtorRef printLogRef printRef hostRef
  numberProtoRef numberCtorRef numberToStringRef numberValueOfRef
  numberIsFiniteRef numberIsIntegerRef numberIsNaNRef numberIsSafeIntegerRef
  booleanProtoRef booleanCtorRef booleanToStringRef booleanValueOfRef
  mathRef mathAbsRef mathCeilRef mathFloorRef mathFroundRef mathRoundRef
  mathSignRef mathSqrtRef mathTruncRef mathMaxRef mathMinRef mathPowRef
  parseFloatRef parseIntRef numberToFixedRef numberToExponentialRef
  numberToPrecisionRef numberToLocaleStringRef
  objectCellRef arrayCellRef stringCellRef printCellRef hostCellRef
  numberCellRef booleanCellRef mathCellRef nanCellRef infinityCellRef
  parseFloatCellRef parseIntCellRef

-- Running a script, and the transformer plumbing core does not tag as
-- `simp` (`Tarski/Monad.lean` says why).
attribute [tarski_eval]
  runScript runProgram evalProgram throwJsError throwCompletion
  ExceptT.run_bind Except.map

-- The library's bridge between the two spellings of a float comparison:
-- a model's guard is a `Prop`, the evaluator's answer is a `Bool`, and
-- an obligation that case-splits one has to see the other.
attribute [tarski_eval] Js.float_lt_prop_eq_bool Js.float_le_prop_eq_bool

/-! ## The guarded steps

Four definitions recurse on the heap. Each is unfolded by a simproc that
fires only when the reference it recurses on has already become a
literal — a prototype link the heap has resolved, or the object a `new`
is constructing. Under an unresolved reference the simproc declines and
the term stands, which is what keeps `simp` terminating. -/

open Lean Meta Simp

-- `Expr` is the evaluator's own AST type in this namespace, so Lean's is
-- spelled out wherever the two would collide.

/-- Whether an expression is a settled `Ref`: a numeral, so the heap has
resolved the link rather than left it under a binder. -/
private def isRefLit (e : Lean.Expr) : Bool := e.nat?.isSome || e.isRawNatLit

/-- Whether an expression is a settled object value, `Value.obj` of a
numeral — what `construct`'s dispatch needs before it can choose an arm. -/
private def isObjLit (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``Tarski.Value.obj 1 && isRefLit e.appArg!

/-- Unfold one step of a heap recursion, but only when the argument it
recurses on has settled. `eqDef` is the definition's `eq_def` theorem and
`arity` the number of arguments it takes; anything applied beyond that —
the monad's own state argument, where a proof has pushed one in — rides
along on `congrFun`. -/
private def unfoldWhen (eqDef : Name) (arity : Nat) (guard : Lean.Expr → Bool)
    (e : Lean.Expr) : SimpM Step := do
  let args := e.getAppArgs
  unless arity > 0 && args.size ≥ arity do return .continue
  unless guard (← instantiateMVars args[0]!) do return .continue
  let mut proof ← mkAppM eqDef (args.extract 0 arity)
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  let mut expr := rhs
  for a in args.extract arity args.size do
    proof ← mkCongrFun proof a
    expr := mkApp expr a
  return .visit { expr := expr, proof? := some proof }

/-- OrdinaryGet's prototype step, taken once the parent is a literal. -/
simproc [tarski_eval] unfoldGetFromUp (getFromUp _ _ _) :=
  unfoldWhen ``Tarski.getFromUp.eq_def 3 isRefLit

/-- OrdinarySet's prototype step, taken once the parent is a literal. -/
simproc [tarski_eval] unfoldFindAccessorUp (findAccessorUp _ _) :=
  unfoldWhen ``Tarski.findAccessorUp.eq_def 2 isRefLit

/-- `[[HasInstance]]`'s walk, taken once the object is a literal. -/
simproc [tarski_eval] unfoldProtoChainHas (protoChainHas _ _) :=
  unfoldWhen ``Tarski.protoChainHas.eq_def 2 isRefLit

/-- `[[Construct]]`, taken once the constructor is a literal object. -/
simproc [tarski_eval] unfoldConstruct (construct _ _ _) :=
  unfoldWhen ``Tarski.construct.eq_def 3 isObjLit

end Tarski
