import Tarski.Realm

/-! The realm's literal against the realm's constants.

`Heap.initial` is written out by hand, and every reference into it —
`ErrorKind.protoRef`, `ctorRef`, `errorToStringRef`, `cellRef`, and the
`Object`, `Array`, and `String` references — is a constant written out
beside it. Nothing makes the two agree except this
file: a prototype moved without its constant, or a constructor pointing
at the wrong `prototype`, would be a realm that is quietly wrong
everywhere rather than a build that fails. So each case below reads one
of the layout's claims back out of the literal by its constant. -/

open Tarski

/-! ## The shape -/

#guard Heap.initial.cells.size == 19
#guard Heap.initial.objects.size == 59

/-! ## Each kind's prototype

`name` and `message` are what `Error.prototype.toString` reads, and
`constructor` is what points back; the `[[Prototype]]` link is what makes
`new TypeError("t") instanceof Error` true. -/

private def protoOf (k : ErrorKind) : Option Obj := Heap.initial.readObj k.protoRef

#guard ErrorKind.all.all fun k =>
  match protoOf k with
  | none => false
  | some o =>
    o.getOwn "name" == some (.prim (.str k.name))
      && o.getOwn "message" == some (.prim (.str ""))
      && o.getOwn "constructor" == some (.obj k.ctorRef)
      && o.proto == (if k == .error then some objectProtoRef else some ErrorKind.error.protoRef)

-- `Error.prototype` is the one that carries `toString`; the subclasses
-- inherit it.
#guard (protoOf .error).bind (fun o => o.getOwn "toString") == some (.obj errorToStringRef)
#guard (protoOf .typeError).bind (fun o => o.getOwn "toString") == none

/-! ## Each kind's constructor

`Obj` has no `DecidableEq` — a `Closure` holds syntax — so `callable` is
matched rather than compared. -/

private def ctorOf (k : ErrorKind) : Option Obj := Heap.initial.readObj k.ctorRef

#guard ErrorKind.all.all fun k =>
  match ctorOf k with
  | none => false
  | some o =>
    o.getOwn "prototype" == some (.obj k.protoRef)
      && o.proto == (if k == .error then none else some ErrorKind.error.ctorRef)
      && (match o.callable with
          | some (.native (.errorCtor k')) => k' == k
          | _ => false)

/-! ## The global bindings

Each constructor is bound under its own `name`, in a cell holding the
constructor object. -/

#guard ErrorKind.all.all fun k =>
  Env.lookup globalEnv k.name == some k.cellRef
    && (match Heap.initial.read k.cellRef with
        | some c => c.value == some (.obj k.ctorRef)
        | none => false)

#guard globalEnv.length == 19

/-! ## `Error.prototype.toString` -/

#guard match Heap.initial.readObj errorToStringRef with
  | some { callable := some (.native .errorToString), .. } => true
  | _ => false

/-! ## `Object.prototype` and `Object`

`hasOwnProperty` is the whole of `Object.prototype`'s surface: `toString`
and `valueOf` are #389's, and `ObjectsTest` pins that `{} + 1` still
throws for want of them. -/

#guard match Heap.initial.readObj objectProtoRef with
  | some o =>
    o.proto == none
      && o.getOwn "constructor" == some (.obj objectCtorRef)
      && o.getOwn "hasOwnProperty" == some (.obj objectHasOwnPropertyRef)
      && o.getOwn "toString" == none
      && o.getOwn "valueOf" == none
      && o.kind == .ordinary
  | none => false

#guard match Heap.initial.readObj objectCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj objectProtoRef)
      && o.getOwn "is" == some (.obj objectIsRef)
      && o.getOwn "keys" == some (.obj objectKeysRef)
      && (match o.callable with
          | some (.native .objectCtor) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj objectHasOwnPropertyRef with
  | some { callable := some (.native .objectHasOwnProperty), .. } => true
  | _ => false

#guard match Heap.initial.readObj objectIsRef with
  | some { callable := some (.native .objectIs), .. } => true
  | _ => false

#guard match Heap.initial.readObj objectKeysRef with
  | some { callable := some (.native .objectKeys), .. } => true
  | _ => false

/-! ## `Array.prototype` and `Array`

`Array.prototype` is itself an array of length 0, which the spec is
explicit about and `Array.isArray(Array.prototype)` observes. -/

#guard match Heap.initial.readObj arrayProtoRef with
  | some o =>
    o.kind == .array 0
      && o.proto == some objectProtoRef
      && o.getOwn "constructor" == some (.obj arrayCtorRef)
      && o.getOwn "push" == some (.obj arrayPushRef)
      && o.getOwn "join" == some (.obj arrayJoinRef)
  | none => false

#guard match Heap.initial.readObj arrayCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj arrayProtoRef)
      && o.getOwn "isArray" == some (.obj arrayIsArrayRef)
      && (match o.callable with
          | some (.native .arrayCtor) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj arrayPushRef with
  | some { callable := some (.native .arrayPush), .. } => true
  | _ => false

#guard match Heap.initial.readObj arrayJoinRef with
  | some { callable := some (.native .arrayJoin), .. } => true
  | _ => false

#guard match Heap.initial.readObj arrayIsArrayRef with
  | some { callable := some (.native .arrayIsArray), .. } => true
  | _ => false

/-! ## `String`

No `prototype` property: the wrapper object and `String.prototype` are
#391's, so `new String("x")` refuses. -/

#guard match Heap.initial.readObj stringCtorRef with
  | some o =>
    o.getOwn "prototype" == none
      && (match o.callable with
          | some (.native .stringCtor) => true
          | _ => false)
  | none => false

/-! ## The three new global bindings -/

#guard Env.lookup globalEnv "Object" == some objectCellRef
#guard Env.lookup globalEnv "Array" == some arrayCellRef
#guard Env.lookup globalEnv "String" == some stringCellRef

#guard (Heap.initial.read objectCellRef).bind (·.value) == some (.obj objectCtorRef)
#guard (Heap.initial.read arrayCellRef).bind (·.value) == some (.obj arrayCtorRef)
#guard (Heap.initial.read stringCellRef).bind (·.value) == some (.obj stringCtorRef)

/-! ## The host bindings

`print` and `$262` are what test262 asks a host for. `%PrintLog%` is the
array `print` appends to: an intrinsic nothing binds, so a run's log is
exactly what `print` put there. `$262` is empty on purpose — its hooks
are decoder refusals, and what is left is an object for `typeof` to see
and an absent `IsHTMLDDA` to read as `undefined`. -/

#guard match Heap.initial.readObj printLogRef with
  | some o => o.kind == .array 0 && o.proto == some arrayProtoRef && o.properties == []
  | none => false

#guard match Heap.initial.readObj printRef with
  | some { callable := some (.native .print), .. } => true
  | _ => false

#guard match Heap.initial.readObj hostRef with
  | some o => o.properties == [] && o.proto == some objectProtoRef && o.callable.isNone
  | none => false

#guard Env.lookup globalEnv "print" == some printCellRef
#guard Env.lookup globalEnv "$262" == some hostCellRef

#guard (Heap.initial.read printCellRef).bind (·.value) == some (.obj printRef)
#guard (Heap.initial.read hostCellRef).bind (·.value) == some (.obj hostRef)

/-! ## `Number.prototype` and `Number`

`Number.prototype` is itself a Number object whose `[[NumberData]]` is
`+0`, as the spec has it, which is what makes `Number.prototype.valueOf()`
answer `0`. Every constant on `Number` is the library's own definition
under its source spelling, so the realm and a `Theorem` name the same
double; the list is walked rather than written out twice. -/

#guard match Heap.initial.readObj numberProtoRef with
  | some o =>
    o.kind == .number 0.0
      && o.proto == some objectProtoRef
      && o.getOwn "constructor" == some (.obj numberCtorRef)
      && o.getOwn "toString" == some (.obj numberToStringRef)
      && o.getOwn "valueOf" == some (.obj numberValueOfRef)
      && o.getOwn "toFixed" == some (.obj numberToFixedRef)
      && o.getOwn "toExponential" == some (.obj numberToExponentialRef)
      && o.getOwn "toPrecision" == some (.obj numberToPrecisionRef)
      && o.getOwn "toLocaleString" == some (.obj numberToLocaleStringRef)
  | none => false

#guard match Heap.initial.readObj numberCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj numberProtoRef)
      && o.getOwn "isFinite" == some (.obj numberIsFiniteRef)
      && o.getOwn "isInteger" == some (.obj numberIsIntegerRef)
      && o.getOwn "isNaN" == some (.obj numberIsNaNRef)
      && o.getOwn "isSafeInteger" == some (.obj numberIsSafeIntegerRef)
      -- The same two objects the globals are bound to, so
      -- `Number.parseInt === parseInt`.
      && o.getOwn "parseFloat" == some (.obj parseFloatRef)
      && o.getOwn "parseInt" == some (.obj parseIntRef)
      && (match o.callable with
          | some (.native .numberCtor) => true
          | _ => false)
  | none => false

private def numberConstants : List (String × Float) :=
  [ ("EPSILON", Js.Number.EPSILON),
    ("MAX_SAFE_INTEGER", Js.Number.MAX_SAFE_INTEGER),
    ("MIN_SAFE_INTEGER", Js.Number.MIN_SAFE_INTEGER),
    ("MAX_VALUE", Js.Number.MAX_VALUE),
    ("MIN_VALUE", Js.Number.MIN_VALUE),
    ("POSITIVE_INFINITY", Js.Number.POSITIVE_INFINITY),
    ("NEGATIVE_INFINITY", Js.Number.NEGATIVE_INFINITY),
    ("NaN", Js.Number.NaN) ]

#guard match Heap.initial.readObj numberCtorRef with
  | some o => numberConstants.all fun p => o.getOwn p.1 == some (.prim (.num p.2))
  | none => false

/-! ## The four `Number.prototype` formatters and the two global parsers

Each is one object with a `[[Call]]` and nothing else, and `parseFloat`
and `parseInt` are each **one** object: the global cell and the property
on `Number` name the same reference, which is what
`Number.parseInt === parseInt` observes. -/

#guard Env.lookup globalEnv "parseFloat" == some parseFloatCellRef
#guard Env.lookup globalEnv "parseInt" == some parseIntCellRef
#guard (Heap.initial.read parseFloatCellRef).bind (·.value) == some (.obj parseFloatRef)
#guard (Heap.initial.read parseIntCellRef).bind (·.value) == some (.obj parseIntRef)

/-! ## `Boolean.prototype` and `Boolean` -/

#guard match Heap.initial.readObj booleanProtoRef with
  | some o =>
    o.kind == .boolean false
      && o.proto == some objectProtoRef
      && o.getOwn "constructor" == some (.obj booleanCtorRef)
      && o.getOwn "toString" == some (.obj booleanToStringRef)
      && o.getOwn "valueOf" == some (.obj booleanValueOfRef)
  | none => false

#guard match Heap.initial.readObj booleanCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj booleanProtoRef)
      && (match o.callable with
          | some (.native .booleanCtor) => true
          | _ => false)
  | none => false

/-! ## `Math`

No `[[Call]]`: `Math()` is `not a function`. Its members are exactly the
ones the library expresses — the transcendental family, `random`,
`clz32`, and `imul` are absent rather than faked. -/

#guard match Heap.initial.readObj mathRef with
  | some o => o.proto == some objectProtoRef && o.callable.isNone
  | none => false

private def mathConstants : List (String × Float) :=
  [ ("E", Js.Math.E),
    ("LN10", Js.Math.LN10),
    ("LN2", Js.Math.LN2),
    ("LOG10E", Js.Math.LOG10E),
    ("LOG2E", Js.Math.LOG2E),
    ("PI", Js.Math.PI),
    ("SQRT1_2", Js.Math.SQRT1_2),
    ("SQRT2", Js.Math.SQRT2) ]

#guard match Heap.initial.readObj mathRef with
  | some o => mathConstants.all fun p => o.getOwn p.1 == some (.prim (.num p.2))
  | none => false

private def mathMembers : List (String × Ref) :=
  [ ("abs", mathAbsRef),
    ("ceil", mathCeilRef),
    ("floor", mathFloorRef),
    ("fround", mathFroundRef),
    ("round", mathRoundRef),
    ("sign", mathSignRef),
    ("sqrt", mathSqrtRef),
    ("trunc", mathTruncRef),
    ("max", mathMaxRef),
    ("min", mathMinRef),
    ("pow", mathPowRef) ]

#guard match Heap.initial.readObj mathRef with
  | some o => mathMembers.all fun p => o.getOwn p.1 == some (.obj p.2)
  | none => false

#guard match Heap.initial.readObj mathRef with
  | some o =>
    ["cbrt", "random", "hypot", "exp", "log", "log2", "log10", "atan2", "sin", "cos",
      "clz32", "imul", "f16round", "sumPrecise"].all fun k => o.getOwn k == none
  | none => false

/-! ## Each native is the one its reference names -/

private def nativeAt (r : Ref) (n : NativeFn) : Bool :=
  match Heap.initial.readObj r with
  | some { callable := some (.native n'), .. } => n' == n
  | _ => false

#guard [ (parseFloatRef, NativeFn.parseFloat),
         (parseIntRef, .parseInt),
         (numberToFixedRef, .numberToFixed),
         (numberToExponentialRef, .numberToExponential),
         (numberToPrecisionRef, .numberToPrecision),
         (numberToLocaleStringRef, .numberToLocaleString) ].all fun p => nativeAt p.1 p.2

#guard [ (numberCtorRef, NativeFn.numberCtor),
         (numberToStringRef, .numberToString),
         (numberValueOfRef, .numberValueOf),
         (numberIsFiniteRef, .numberIsFinite),
         (numberIsIntegerRef, .numberIsInteger),
         (numberIsNaNRef, .numberIsNaN),
         (numberIsSafeIntegerRef, .numberIsSafeInteger),
         (booleanCtorRef, .booleanCtor),
         (booleanToStringRef, .booleanToString),
         (booleanValueOfRef, .booleanValueOf),
         (mathAbsRef, .mathAbs),
         (mathCeilRef, .mathCeil),
         (mathFloorRef, .mathFloor),
         (mathFroundRef, .mathFround),
         (mathRoundRef, .mathRound),
         (mathSignRef, .mathSign),
         (mathSqrtRef, .mathSqrt),
         (mathTruncRef, .mathTrunc),
         (mathMaxRef, .mathMax),
         (mathMinRef, .mathMin),
         (mathPowRef, .mathPow) ].all fun p => nativeAt p.1 p.2

/-! ## The five new global bindings

`Number`, `Boolean`, and `Math` are writable cells like every other
global function binding. `NaN` and `Infinity` are the global object's
non-writable value properties, so their cells are immutable and hold the
library's own constants — which is what makes `NaN = 1` a strict-mode
`TypeError`. -/

#guard Env.lookup globalEnv "Number" == some numberCellRef
#guard Env.lookup globalEnv "Boolean" == some booleanCellRef
#guard Env.lookup globalEnv "Math" == some mathCellRef
#guard Env.lookup globalEnv "NaN" == some nanCellRef
#guard Env.lookup globalEnv "Infinity" == some infinityCellRef

#guard (Heap.initial.read numberCellRef).bind (·.value) == some (.obj numberCtorRef)
#guard (Heap.initial.read booleanCellRef).bind (·.value) == some (.obj booleanCtorRef)
#guard (Heap.initial.read mathCellRef).bind (·.value) == some (.obj mathRef)

#guard (Heap.initial.read numberCellRef).map (·.mutable) == some true
#guard (Heap.initial.read booleanCellRef).map (·.mutable) == some true
#guard (Heap.initial.read mathCellRef).map (·.mutable) == some true

#guard (Heap.initial.read nanCellRef).map (·.mutable) == some false
#guard (Heap.initial.read infinityCellRef).map (·.mutable) == some false
#guard (Heap.initial.read nanCellRef).bind (·.value) == some (.prim (.num Js.Number.NaN))
#guard (Heap.initial.read infinityCellRef).bind (·.value)
  == some (.prim (.num Js.Number.POSITIVE_INFINITY))
