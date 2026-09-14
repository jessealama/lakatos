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
`evalWhile`, `evalDoWhile`, `evalFor`, `evalForOf`, and `joinElements`,
whose tests are the `*UnfoldTest` files. A definition that recurses on the *heap* is in
between: it stops as soon as the heap says so, but `simp` will unfold it
forever under a reference it has not yet resolved. Those four —
`getFromUp`, `findPropertyUp`, `protoChainHas`, and `construct` — join
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
ninety-two-object literal heap is something `simp` pushes `readObj`
through.

**What stays outside.** The list walks a native performs —
`listFromArrayLike` for `apply`, and `forInNext`, the step from one
object of a `for`-`in` to its prototype — recurse the way a loop does,
and so do the three steps a bound function's target is reached by,
`callBound`, `constructBound`, and `instanceOfBound`; each is `rw`'s and
none is here. `rawSegments`, `String.raw`'s walk, is one of them.
`callStringNative`, the `String` surface, is out for `callReflectNative`'s
reason rather than for a loop's. So are the four walks that run until an
*iterator* says stop: `evalForOf`, `iteratorToList`, `fromEntriesInto`,
and `groupByInto`. -/

namespace Tarski

open Js

/-! ## The equations

One block, grouped the way the tests' lists were. Every name here
recurses on syntax or not at all. -/

-- Evaluation proper, and the instantiation a block is preceded by.
-- `evalNamed` is NamedEvaluation, a dispatch onto `evalExpr`.
attribute [tarski_eval]
  evalExpr evalCallee evalExprs evalArgs evalArrayElements defineFrom
  evalStmt evalStmts evalPropDefs evalPropKey
  evalTemplate getTemplateObject evalDeclarators evalBlock evalNamed
  evalForInLoop evalForIn bindForIn evalForOfLoop
  instantiateBlock hoistNames hoistDeclarators allocNames initFunctions

-- The iteration protocol and destructuring. `getIterator`,
-- `iteratorStep`, and `iteratorClose` call user code and stop; the
-- pattern walk recurses on syntax; `callIteratorNative` is split out of
-- `callNative` for `callReflectNative`'s reason but is **in** the set,
-- its seven arms being far below the equation-lemma ceiling — which is
-- what lets a closed destructuring or one `for`-`of` step reduce with no
-- local lemma list at all.
attribute [tarski_eval]
  getIterator iteratorStep iteratorClose createIterResult
  evalLeafRef writeLeaf patternLeafRef bindOne bindPattern bindProps bindElements bindRest
  copyDataProperties copyKeys callIteratorNative
  Pattern.boundNames patternElemsNames patternPropsNames patternRestNames targetBoundNames
  Pattern.containsExpression patternElemsContain patternPropsContain patternRestContains
  PropKey.isComputed

-- `var` hoisting: VarDeclaredNames over a body, and the cells it gives them.
attribute [tarski_eval]
  varNames varNamesStmt varNamesCases hoistVars

-- Calls: user code, built-ins, and the two opaque catch sites.
-- `callReflectNative`, the `Object` and `Function` surface `callNative`
-- defers to, is not here: its twenty-nine arms are past the depth at
-- which Lean generates a match's equation lemmas, so registering it
-- overflows `maxRecDepth` before any proof runs (#471's ceiling, seen
-- from the other side). `callSymbolNative` and `callJsonNative`, the two
-- groups `callNative` defers the `Symbol` surface and `JSON` to, stay
-- out for that same reason, and with them the heap walks they own —
-- `jsonToValue`, `internalizeJsonProperty`, and the `serializeJson*`
-- family: no proof today reads a symbol or a JSON text.
attribute [tarski_eval]
  callFunction callNative constructNative catchReturn attempt liftCompletion
  makeFunction isConstructor NativeFn.constructs nameOf functionSourceText builtinTag
  toStringValue toStringValues toNumberValue toNumberValues toLengthValue mathUnary pushElements
  ordinaryHasInstance installErrorCause

-- FunctionDeclarationInstantiation: parameters, their defaults, the
-- `var`s a body hoists past them, and the `arguments` object a body that
-- mentions the name is given. `mentionsArguments` is a syntactic scan.
attribute [tarski_eval]
  instantiateFunction allocParams initParams hoistVarsFrom
  Param.names hasDefaults expectedArgumentCount
  makeArguments argumentsName mentionsArguments
  mentionsArgumentsExpr mentionsArgumentsExprs
  mentionsArgumentsPropDefs mentionsArgumentsPropKey
  mentionsArgumentsTarget mentionsArgumentsArrow mentionsArgumentsParams
  mentionsArgumentsClass mentionsArgumentsStmts mentionsArgumentsStmt
  mentionsArgumentsForInit mentionsArgumentsDecls mentionsArgumentsCases
  mentionsArgumentsPattern mentionsArgumentsElems mentionsArgumentsProps
  mentionsArgumentsPatternOpt

-- Classes and private elements.
attribute [tarski_eval]
  evalClass defineMethods initializeInstance initFields initFieldList
  constructClass runConstructor superConstructor bindPrivateNames privateName
  readPrivate writePrivate addPrivate allocFromConstructor
  ClassDef.constructor? ClassDef.instanceFields ClassDef.staticFields
  ClassDef.privateNames classFields dedupNames firstConstructor privateFieldNames

-- Property reads and writes, own-property depth only: the two prototype
-- steps are guarded simprocs below. The property protocol's own
-- operations — `[[Delete]]`, `[[HasProperty]]`, `[[DefineOwnProperty]]`
-- through a descriptor, and the enumeration helpers over a concrete key
-- list — recurse on data or not at all.
attribute [tarski_eval]
  getProp setProp getFrom findProperty hasProperty deleteProp toObjectValue
  descriptorField toDescriptor fromProperty refuseDefine defineArrayLength
  definePropertyOrThrow readDescriptors applyDescriptors defineProperties
  enumerableOwn assignKeys assignSources descriptorsInto

-- The `Obj` operations, the one property list they keep, and the
-- descriptor table over it.
attribute [tarski_eval]
  Obj.getOwn Obj.setOwn Obj.getOwnAccessor Obj.getOwnProperty Obj.ownProperty
  Obj.getPrivate Obj.setPrivate Obj.addPrivate
  Obj.define Obj.defineAccessorHalf Obj.remove Obj.isArray Obj.arrayLength? Obj.hasOwn
  Obj.ownKeys Obj.stringKeys Obj.symbolKeys Obj.enumerableKeys Obj.truncate truncateDrop
  Obj.setIntegrity Obj.testIntegrity Obj.applyDescriptor Obj.applyOrdinaryDescriptor
  Obj.array indexProps
  propGet propSet propDrop privateGet privateSet
  Property.value? Property.writable? Property.accessor? Property.isAccessor
  Property.toDescriptor Property.accepts
  Descriptor.isAccessor Descriptor.isData Descriptor.isGeneric
  Descriptor.isEmpty accessorHalf descriptorKeeps

-- Operators and coercions. Every primitive operation is the library's;
-- the evaluator only dispatches onto it.
attribute [tarski_eval]
  applyBinary applyUnary applyStrict applyCoercing BinaryOp.coerces
  toPrimitive toNumberPrim toBooleanPrim toStringPrim isStrPrim PrimHint.name
  symbolOperandRefusal
  strictEqValue sameValueValue Js.JsVal.strictEq Value.ofNat

-- Keys and symbols.
attribute [tarski_eval]
  Key.beq Key.str? Key.sym? Key.arrayIndex? Key.functionName
  Symbol.descriptiveString allocSymbol thisSymbolValue registryKeyFor


/-! ## The coercions, on a primitive

ToPrimitive answers a `Value` now, so a coercion of a primitive is a
`match` on a constructor `simp` has to push through at every arithmetic
step. These three close that case in one rewrite instead, which is what
keeps the `*UnfoldTest` files — each of which coerces once per
iteration — near where they were. -/

@[tarski_eval] theorem applyCoercing_prim (op : BinaryOp) (a b : Js.JsVal) :
    applyCoercing op (.prim a) (.prim b) = pure (applyBinary op a b) := by
  cases op <;> (rw [applyCoercing]; simp [toPrimitive]) <;> simp

@[tarski_eval] theorem toNumberValue_prim (p : Js.JsVal) :
    toNumberValue (.prim p) = pure (toNumberPrim p) := by
  rw [toNumberValue]; simp [toPrimitive]

@[tarski_eval] theorem toStringValue_prim (p : Js.JsVal) :
    toStringValue (.prim p) = pure (toStringPrim p) := by
  rw [toStringValue]; simp [toPrimitive]

-- Strings. **No `JsString` definition is an unfolding here**, and
-- `JsString.ofString` least of all: a string literal stays folded, and
-- `ofString_append` is what lets a concatenation fold with it, so `simp`
-- never opens a string into its code units and a reduction's string
-- terms stay the size they were when a string was a Lean `String`.
-- Unfolding `ofString` is what a proof about a *string operation* would
-- need, and it can ask for it by name.
attribute [tarski_eval] Js.JsString.ofString_append

-- The String exotic object, and the `String` surface's dispatch.
-- `callStringNative` is **not** here, for `callReflectNative`'s reason:
-- thirty-four arms is past the depth at which Lean generates a match's
-- equation lemmas. Neither is `rawSegments`, which recurses on a length
-- the heap named, as `joinElements` does.
attribute [tarski_eval]
  Obj.stringWrapper Obj.stringIndexProperty Obj.isString Obj.stringData?
  argAt requireStringThis thisStringValue toUint32Value toUint16Value toUint16Values
  relativeArg clampArg

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
  numberToPrecisionRef numberToLocaleStringRef throwTypeErrorRef consoleRef consoleLogRef
  functionProtoRef functionCtorRef functionCallRef functionApplyRef functionBindRef
  functionToStringRef objectProtoToStringRef objectProtoValueOfRef
  objectProtoToLocaleStringRef objectProtoIsPrototypeOfRef
  objectProtoPropertyIsEnumerableRef objectAssignRef objectCreateRef
  objectDefinePropertiesRef objectDefinePropertyRef objectEntriesRef objectFreezeRef
  objectGetOwnPropertyDescriptorRef objectGetOwnPropertyDescriptorsRef
  objectGetOwnPropertyNamesRef objectGetPrototypeOfRef objectHasOwnRef
  objectIsExtensibleRef objectIsFrozenRef objectIsSealedRef objectPreventExtensionsRef
  objectSealRef objectSetPrototypeOfRef objectValuesRef templateMapRef
  stringProtoRef StringFn.ref StringFn.all
  objectCellRef arrayCellRef stringCellRef printCellRef hostCellRef
  numberCellRef booleanCellRef mathCellRef nanCellRef infinityCellRef
  parseFloatCellRef parseIntCellRef consoleCellRef functionCellRef
  symbolProtoRef symbolCtorRef symbolForRef symbolKeyForRef symbolProtoToStringRef
  symbolProtoValueOfRef symbolDescriptionRef symbolToPrimitiveRef symbolRegistryRef
  jsonRef jsonParseRef jsonStringifyRef
  aggregateErrorProtoRef aggregateErrorCtorRef functionHasInstanceRef
  objectGetOwnPropertySymbolsRef errorIsErrorRef
  iteratorProtoRef iteratorProtoIteratorRef arrayIteratorProtoRef arrayIteratorNextRef
  arrayKeysRef arrayValuesRef arrayEntriesRef objectFromEntriesRef objectGroupByRef
  symbolCellRef jsonCellRef aggregateErrorCellRef wellKnownSymbolCellBase
  WellKnownSymbol.name WellKnownSymbol.description WellKnownSymbol.id
  WellKnownSymbol.symbol WellKnownSymbol.key WellKnownSymbol.all

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
simproc [tarski_eval] unfoldFindPropertyUp (findPropertyUp _ _) :=
  unfoldWhen ``Tarski.findPropertyUp.eq_def 2 isRefLit

/-- `[[HasInstance]]`'s walk, taken once the object is a literal. -/
simproc [tarski_eval] unfoldProtoChainHas (protoChainHas _ _) :=
  unfoldWhen ``Tarski.protoChainHas.eq_def 2 isRefLit

/-- `[[Construct]]`, taken once the constructor is a literal object. -/
simproc [tarski_eval] unfoldConstruct (construct _ _ _) :=
  unfoldWhen ``Tarski.construct.eq_def 3 isObjLit

end Tarski
