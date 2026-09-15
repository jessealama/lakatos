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

#guard Heap.initial.cells.size == 37
#guard Heap.initial.objects.size == 156

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
      && o.proto == (if k == .error then some functionProtoRef else some ErrorKind.error.ctorRef)
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

#guard globalEnv.length == 24

/-! ## `Error.prototype.toString` -/

#guard match Heap.initial.readObj errorToStringRef with
  | some { callable := some (.native .errorToString), .. } => true
  | _ => false

/-! ## `Object.prototype` and `Object`

`Object.prototype` carries the whole of 20.1.3 but `__proto__` (#487)
and `@@toStringTag` (#392); `Object` carries the whole of 20.1.2 but
`getOwnPropertySymbols` (#392). -/

#guard match Heap.initial.readObj objectProtoRef with
  | some o =>
    o.proto == none
      && o.getOwn "constructor" == some (.obj objectCtorRef)
      && o.getOwn "hasOwnProperty" == some (.obj objectHasOwnPropertyRef)
      && o.getOwn "toString" == some (.obj objectProtoToStringRef)
      && o.getOwn "valueOf" == some (.obj objectProtoValueOfRef)
      && o.getOwn "toLocaleString" == some (.obj objectProtoToLocaleStringRef)
      && o.getOwn "isPrototypeOf" == some (.obj objectProtoIsPrototypeOfRef)
      && o.getOwn "propertyIsEnumerable" == some (.obj objectProtoPropertyIsEnumerableRef)
      && o.getOwn "__proto__" == none
      && o.kind == .ordinary
  | none => false

private def objectStatics : List (String × Ref) :=
  [ ("assign", objectAssignRef),
    ("create", objectCreateRef),
    ("defineProperties", objectDefinePropertiesRef),
    ("defineProperty", objectDefinePropertyRef),
    ("entries", objectEntriesRef),
    ("freeze", objectFreezeRef),
    ("fromEntries", objectFromEntriesRef),
    ("getOwnPropertyDescriptor", objectGetOwnPropertyDescriptorRef),
    ("getOwnPropertyDescriptors", objectGetOwnPropertyDescriptorsRef),
    ("getOwnPropertyNames", objectGetOwnPropertyNamesRef),
    ("getPrototypeOf", objectGetPrototypeOfRef),
    ("groupBy", objectGroupByRef),
    ("hasOwn", objectHasOwnRef),
    ("is", objectIsRef),
    ("isExtensible", objectIsExtensibleRef),
    ("isFrozen", objectIsFrozenRef),
    ("isSealed", objectIsSealedRef),
    ("keys", objectKeysRef),
    ("preventExtensions", objectPreventExtensionsRef),
    ("seal", objectSealRef),
    ("setPrototypeOf", objectSetPrototypeOfRef),
    ("values", objectValuesRef) ]

#guard match Heap.initial.readObj objectCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj objectProtoRef)
      && objectStatics.all (fun p => o.getOwn p.1 == some (.obj p.2))
      && (match o.callable with
          | some (.native .objectCtor) => true
          | _ => false)
  | none => false

/-! ## `Function.prototype` and `Function`

`Function.prototype` is itself a function — 20.2.3 makes it callable and
has it answer `undefined` — and it is the one function object whose
`[[Prototype]]` is `Object.prototype` rather than itself. Its `name` is
the empty string. -/

#guard match Heap.initial.readObj functionProtoRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.getOwn "name" == some (.prim (.str ""))
      && o.getOwn "length" == some (Value.ofNat 0)
      && o.getOwn "constructor" == some (.obj functionCtorRef)
      && o.getOwn "call" == some (.obj functionCallRef)
      && o.getOwn "apply" == some (.obj functionApplyRef)
      && o.getOwn "bind" == some (.obj functionBindRef)
      && o.getOwn "toString" == some (.obj functionToStringRef)
      && o.getOwn "prototype" == none
      && (match o.callable with
          | some (.native .functionProto) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj functionCtorRef with
  | some o =>
    o.proto == some functionProtoRef
      && o.getOwn "prototype" == some (.obj functionProtoRef)
      && o.getOwn "name" == some (.prim (.str "Function"))
      && (match o.callable with
          | some (.native .functionCtor) => true
          | _ => false)
  | none => false

#guard Env.lookup globalEnv "Function" == some functionCellRef
#guard (Heap.initial.read functionCellRef).bind (·.value) == some (.obj functionCtorRef)

/-! ## Every function object links to `Function.prototype`

That is what `f.call`, `f.bind`, and `(function () {}) instanceof
Function` all read through. The one exception is `Function.prototype`
itself, whose own `[[Prototype]]` is `Object.prototype`; the `Error`
subclass constructors link to `Error`, which links to
`Function.prototype` in its turn. -/

#guard (List.range Heap.initial.objects.size).all fun r =>
  match Heap.initial.readObj r with
  | some o =>
    if o.callable.isNone then true
    else if r == functionProtoRef then o.proto == some objectProtoRef
    else o.proto.isSome
  | none => false

#guard (List.range Heap.initial.objects.size).all fun r =>
  match Heap.initial.readObj r with
  | some o =>
    if o.callable.isNone || r == functionProtoRef then true
    else
      -- Either linked straight to `Function.prototype`, or — for the six
      -- `Error` subclass constructors — to `Error`, which is.
      o.proto == some functionProtoRef || o.proto == some ErrorKind.error.ctorRef
  | none => false

/-! ## Property attributes

Every built-in function has a non-writable, non-enumerable,
configurable `length` and `name`, in that order (17.1), `%ThrowTypeError%`'s
alone being non-configurable (10.2.4.1); a method is
writable and configurable but never enumerable; a constructor's
`prototype` and every `Number` and `Math` constant have no attribute at
all. -/

#guard (List.range Heap.initial.objects.size).all fun r =>
  match Heap.initial.readObj r with
  | some o =>
    if o.callable.isNone then true
    else
      match o.properties with
      | ("length", lp) :: ("name", np) :: _ =>
        -- `%ThrowTypeError%` is the exception 10.2.4.1 makes: both of
        -- its own properties are non-configurable too, so a script that
        -- reaches it through `arguments.callee` cannot redefine either.
        [lp, np].all fun p =>
          !p.enumerable && p.configurable == (r != throwTypeErrorRef)
            && p.writable? == some false
      | _ => false
  | none => false

#guard match (Heap.initial.readObj numberCtorRef).bind (·.getOwnProperty "EPSILON") with
  | some p => !p.enumerable && !p.configurable && p.writable? == some false
  | none => false

#guard match (Heap.initial.readObj objectProtoRef).bind (·.getOwnProperty "hasOwnProperty") with
  | some p => !p.enumerable && p.configurable && p.writable? == some true
  | none => false

#guard match (Heap.initial.readObj ErrorKind.error.protoRef).bind (·.getOwnProperty "name") with
  | some p => !p.enumerable && p.configurable && p.writable? == some true
  | none => false

#guard match (Heap.initial.readObj objectCtorRef).bind (·.getOwnProperty "prototype") with
  | some p => !p.enumerable && !p.configurable && p.writable? == some false
  | none => false

/-! ## `[[ErrorData]]` is on the instances, not on the prototypes

`Object.prototype.toString.call(Error.prototype)` is `[object Object]`,
which is what the suite checks; `throwJsError` and the `Error`
constructors are what set the kind. -/

#guard ErrorKind.all.all fun k =>
  match Heap.initial.readObj k.protoRef with
  | some o => o.kind == .ordinary
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
    o.kind == .array 0 true
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

`String` carries its `prototype` and its three statics, and
`String.prototype` is itself a String exotic object of the empty string,
as 22.1.3 has it — so `Object.prototype.toString.call(String.prototype)`
is `[object String]` and `String.prototype.length` is `0`.

The table below is the whole surface, and it is read three ways: each
member's object is at `StringFn.ref`, carries that member's `NativeFn`,
and has 17.1's `name` and `length`; and `String.prototype`'s property
list is the thirty-one prototype members **in `StringFn.all`'s order**,
after `length` and `constructor`. -/

#guard match Heap.initial.readObj stringCtorRef with
  | some o =>
    o.getOwn "prototype" == some (.obj stringProtoRef)
      && o.getOwn "fromCharCode" == some (.obj (StringFn.ref .fromCharCode))
      && o.getOwn "fromCodePoint" == some (.obj (StringFn.ref .fromCodePoint))
      && o.getOwn "raw" == some (.obj (StringFn.ref .raw))
      && (match o.callable with
          | some (.native .stringCtor) => true
          | _ => false)
  | none => false

#guard match Heap.initial.readObj stringProtoRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.kind == .string (Js.JsString.ofString "")
      && o.getOwnProperty "length" == some (Property.constant (Value.ofNat 0))
      && o.getOwn "constructor" == some (.obj stringCtorRef)
  | none => false

/-- Every `String` member: its constructor, its `name`, and 17.1's
`length`. -/
private def stringMembers : List (StringFn × String × Nat) :=
  [
    (.fromCharCode, "fromCharCode", 1),
    (.fromCodePoint, "fromCodePoint", 1),
    (.raw, "raw", 1),
    (.at, "at", 1),
    (.charAt, "charAt", 1),
    (.charCodeAt, "charCodeAt", 1),
    (.codePointAt, "codePointAt", 1),
    (.concat, "concat", 1),
    (.endsWith, "endsWith", 1),
    (.includes, "includes", 1),
    (.indexOf, "indexOf", 1),
    (.isWellFormed, "isWellFormed", 0),
    (.lastIndexOf, "lastIndexOf", 1),
    (.localeCompare, "localeCompare", 1),
    (.normalize, "normalize", 0),
    (.padEnd, "padEnd", 1),
    (.padStart, "padStart", 1),
    (.«repeat», "repeat", 1),
    (.replace, "replace", 2),
    (.replaceAll, "replaceAll", 2),
    (.slice, "slice", 2),
    (.split, "split", 2),
    (.startsWith, "startsWith", 1),
    (.substring, "substring", 2),
    (.toLocaleLowerCase, "toLocaleLowerCase", 0),
    (.toLocaleUpperCase, "toLocaleUpperCase", 0),
    (.toLowerCase, "toLowerCase", 0),
    (.«toString», "toString", 0),
    (.«toUpperCase», "toUpperCase", 0),
    (.toWellFormed, "toWellFormed", 0),
    (.trim, "trim", 0),
    (.trimEnd, "trimEnd", 0),
    (.trimStart, "trimStart", 0),
    (.valueOf, "valueOf", 0) ]

-- The table is `StringFn.all`, in order: nothing is missing and nothing
-- is there twice.
#guard stringMembers.map (·.1) == StringFn.all

-- Each member's object is at its reference, with its native and 17.1's
-- shape.
#guard stringMembers.all fun m =>
  match Heap.initial.readObj (StringFn.ref m.1) with
  | some o =>
    (match o.callable with
     | some (.native (.string g)) => g == m.1
     | _ => false)
      && o.proto == some functionProtoRef
      && o.getOwn "name" == some (.prim (.str m.2.1))
      && o.getOwn "length" == some (Value.ofNat m.2.2)
  | none => false

-- `String.prototype`'s property list is `length`, `constructor`, the
-- thirty-one methods in `StringFn.all`'s order, and then `@@iterator`,
-- which is a symbol key and so last (`Obj.ownKeys`).
#guard match Heap.initial.readObj stringProtoRef with
  | some o =>
    o.properties.map (·.1)
      == ("length" :: "constructor" :: (stringMembers.drop 3).map (·.2.1)).map Key.str
        ++ [WellKnownSymbol.iterator.key]
  | none => false

-- The regex-taking members, the iterator, and Annex B are *not* here:
-- each is out of scope and a call of one is `not a function`.
#guard match Heap.initial.readObj stringProtoRef with
  | some o =>
    ["match", "matchAll", "search", "substr", "trimLeft", "trimRight", "anchor"].all
      (fun k => o.getOwn k == none)
  | none => false

/-! ## The `Object`, `Array`, and `String` global bindings -/

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
  | some o => o.kind == .array 0 true && o.proto == some arrayProtoRef && o.properties == []
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

/-! `console` is not one of test262's: it is `lakatos exe`'s, the binding
an ordinary program writes through. It carries `log` and nothing else,
and `log` writes to the same `%PrintLog%` `print` does. -/

#guard match Heap.initial.readObj consoleRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.callable.isNone
      && o.properties == [(Key.str "log", Property.method (.obj consoleLogRef))]
  | none => false

#guard match Heap.initial.readObj consoleLogRef with
  | some { callable := some (.native .consoleLog), .. } => true
  | _ => false

#guard Env.lookup globalEnv "console" == some consoleCellRef
#guard (Heap.initial.read consoleCellRef).bind (·.value) == some (.obj consoleRef)
#guard (Heap.initial.read consoleCellRef).map (·.mutable) == some true

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

/-! ## `%TemplateMap%`

The realm's `[[TemplateMap]]` starts as a bare object with a null
prototype, no properties, and nothing callable: GetTemplateObject is the
only thing that ever writes to it, and no source name reaches it. -/

#guard match Heap.initial.readObj templateMapRef with
  | some o => o.proto == none && o.properties.isEmpty && o.callable.isNone
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
         (numberToLocaleStringRef, .numberToLocaleString),
         -- %ThrowTypeError%: one object per realm, so `arguments.callee`'s
         -- getter and setter are the same function.
         (throwTypeErrorRef, .throwTypeError) ].all fun p => nativeAt p.1 p.2

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
         (mathPowRef, .mathPow),
         (functionProtoRef, .functionProto),
         (functionCtorRef, .functionCtor),
         (functionCallRef, .functionCall),
         (functionApplyRef, .functionApply),
         (functionBindRef, .functionBind),
         (functionToStringRef, .functionToString),
         (objectProtoToStringRef, .objectProtoToString),
         (objectProtoValueOfRef, .objectProtoValueOf),
         (objectProtoToLocaleStringRef, .objectProtoToLocaleString),
         (objectProtoIsPrototypeOfRef, .objectProtoIsPrototypeOf),
         (objectProtoPropertyIsEnumerableRef, .objectProtoPropertyIsEnumerable),
         (objectAssignRef, .objectAssign),
         (objectCreateRef, .objectCreate),
         (objectDefinePropertiesRef, .objectDefineProperties),
         (objectDefinePropertyRef, .objectDefineProperty),
         (objectEntriesRef, .objectEntries),
         (objectFreezeRef, .objectFreeze),
         (objectGetOwnPropertyDescriptorRef, .objectGetOwnPropertyDescriptor),
         (objectGetOwnPropertyDescriptorsRef, .objectGetOwnPropertyDescriptors),
         (objectGetOwnPropertyNamesRef, .objectGetOwnPropertyNames),
         (objectGetPrototypeOfRef, .objectGetPrototypeOf),
         (objectHasOwnRef, .objectHasOwn),
         (objectIsExtensibleRef, .objectIsExtensible),
         (objectIsFrozenRef, .objectIsFrozen),
         (objectIsSealedRef, .objectIsSealed),
         (objectPreventExtensionsRef, .objectPreventExtensions),
         (objectSealRef, .objectSeal),
         (objectSetPrototypeOfRef, .objectSetPrototypeOf),
         (objectValuesRef, .objectValues) ].all fun p => nativeAt p.1 p.2

/-! ## The iterators

The twelve objects #394 appended: `%IteratorPrototype%` and its
`@@iterator`, `%ArrayIteratorPrototype%` and its `next`, the three
`Array.prototype` iterator-producing methods, the two `Object` members
that consume an iterable, and `%StringIteratorPrototype%` with its `next`
and `String.prototype[@@iterator]`. Neither prototype has a global
binding: nothing in source names one.

`Array.prototype[@@iterator]` **is** `Array.prototype.values`
(23.1.3.40), one object and not two, and an `arguments` object's
`@@iterator` is that same object. -/

#guard [ (iteratorProtoIteratorRef, NativeFn.iteratorProtoIterator, "[Symbol.iterator]", 0),
         (arrayIteratorNextRef, .arrayIteratorNext, "next", 0),
         (arrayKeysRef, .arrayKeys, "keys", 0),
         (arrayValuesRef, .arrayValues, "values", 0),
         (arrayEntriesRef, .arrayEntries, "entries", 0),
         (objectFromEntriesRef, .objectFromEntries, "fromEntries", 1),
         (objectGroupByRef, .objectGroupBy, "groupBy", 2),
         (stringIteratorNextRef, .stringIteratorNext, "next", 0),
         (stringProtoIteratorRef, .stringProtoIterator, "[Symbol.iterator]", 0) ].all fun p =>
  match Heap.initial.readObj p.1 with
  | some o =>
    (match o.callable with
     | some (.native f) => f == p.2.1
     | _ => false)
      && o.getOwn "name" == some (.prim (.str p.2.2.1))
      && o.getOwn "length" == some (.prim (.num p.2.2.2.toFloat))
      && o.proto == some functionProtoRef
  | none => false

#guard match Heap.initial.readObj iteratorProtoRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.getOwn WellKnownSymbol.iterator.key == some (.obj iteratorProtoIteratorRef)
  | none => false

#guard match Heap.initial.readObj arrayIteratorProtoRef with
  | some o =>
    o.proto == some iteratorProtoRef
      && o.getOwn "next" == some (.obj arrayIteratorNextRef)
      && o.getOwn WellKnownSymbol.toStringTag.key
        == some (.prim (.str "Array Iterator"))
  | none => false

#guard match Heap.initial.readObj stringIteratorProtoRef with
  | some o =>
    o.proto == some iteratorProtoRef
      && o.getOwn "next" == some (.obj stringIteratorNextRef)
      && o.getOwn WellKnownSymbol.toStringTag.key
        == some (.prim (.str "String Iterator"))
  | none => false

#guard match Heap.initial.readObj stringProtoRef with
  | some o =>
    o.getOwn WellKnownSymbol.iterator.key == some (.obj stringProtoIteratorRef)
  | none => false

#guard match Heap.initial.readObj arrayProtoRef with
  | some o =>
    o.getOwn "entries" == some (.obj arrayEntriesRef)
      && o.getOwn "keys" == some (.obj arrayKeysRef)
      && o.getOwn "values" == some (.obj arrayValuesRef)
      && o.getOwn WellKnownSymbol.iterator.key == some (.obj arrayValuesRef)
  | none => false

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

/-! ## `Symbol`, `JSON`, and `AggregateError`

The seventeen objects and sixteen cells this slice appended. The
thirteen identity cells are the well-known symbols': a symbol's identity
*is* a cell, so they are allocated like any other binding, and they are
immutable, empty, and never read. -/

#guard Env.lookup globalEnv "Symbol" == some symbolCellRef
#guard Env.lookup globalEnv "JSON" == some jsonCellRef
#guard Env.lookup globalEnv "AggregateError" == some aggregateErrorCellRef
#guard (Heap.initial.read symbolCellRef).bind (·.value) == some (.obj symbolCtorRef)
#guard (Heap.initial.read jsonCellRef).bind (·.value) == some (.obj jsonRef)
#guard (Heap.initial.read aggregateErrorCellRef).bind (·.value)
  == some (.obj aggregateErrorCtorRef)
#guard (Heap.initial.read symbolCellRef).map (·.mutable) == some true
#guard (Heap.initial.read jsonCellRef).map (·.mutable) == some true
#guard (Heap.initial.read aggregateErrorCellRef).map (·.mutable) == some true

-- The thirteen identity cells, in 6.1.5.1's order, starting where the
-- three bindings above leave off.
#guard WellKnownSymbol.all.map (·.id)
  == (List.range 13).map (fun i => wellKnownSymbolCellBase + i)
#guard WellKnownSymbol.all.all fun w =>
  match Heap.initial.read w.id with
  | some c => !c.mutable && c.value.isNone
  | none => false

/-- The built-in function at a reference, with its `length` and `name`
read back out of the literal — 17.1's shape, which is what
`Object.getOwnPropertyNames` on any of these starts with. -/
private def builtinShape (r : Ref) (f : NativeFn) (name : String) (length : Nat) : Bool :=
  match Heap.initial.readObj r with
  | some o =>
    o.proto == some functionProtoRef
      && (match o.callable with | some (.native g) => g == f | _ => false)
      && o.getOwnProperty "length" == some (Property.attribute (Value.ofNat length))
      && o.getOwnProperty "name" == some (Property.attribute (.prim (.str name)))
  | none => false

#guard builtinShape symbolCtorRef .symbolCtor "Symbol" 0
#guard builtinShape symbolForRef .symbolFor "for" 1
#guard builtinShape symbolKeyForRef .symbolKeyFor "keyFor" 1
#guard builtinShape symbolProtoToStringRef .symbolProtoToString "toString" 0
#guard builtinShape symbolProtoValueOfRef .symbolProtoValueOf "valueOf" 0
#guard builtinShape symbolDescriptionRef .symbolDescription "get description" 0
#guard builtinShape symbolToPrimitiveRef .symbolToPrimitive "[Symbol.toPrimitive]" 1
#guard builtinShape jsonParseRef .jsonParse "parse" 2
#guard builtinShape jsonStringifyRef .jsonStringify "stringify" 3
#guard builtinShape functionHasInstanceRef .functionHasInstance "[Symbol.hasInstance]" 1
#guard builtinShape objectGetOwnPropertySymbolsRef .objectGetOwnPropertySymbols
  "getOwnPropertySymbols" 1
#guard builtinShape errorIsErrorRef .errorIsError "isError" 1

/-! `Symbol.prototype`: the two methods, the `description` accessor whose
setter half is absent, and the two symbol-keyed members. -/

#guard match Heap.initial.readObj symbolProtoRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.callable.isNone
      && o.getOwnProperty "constructor" == some (Property.method (.obj symbolCtorRef))
      && o.getOwnProperty "toString" == some (Property.method (.obj symbolProtoToStringRef))
      && o.getOwnProperty "valueOf" == some (Property.method (.obj symbolProtoValueOfRef))
      && o.getOwnProperty "description"
        == some { slot := .accessor { getter := some (.obj symbolDescriptionRef) },
                  enumerable := false, configurable := true }
      && o.getOwnProperty WellKnownSymbol.toPrimitive.key
        == some (Property.attribute (.obj symbolToPrimitiveRef))
      && o.getOwnProperty WellKnownSymbol.toStringTag.key
        == some (Property.attribute (.prim (.str "Symbol")))
  | none => false

/-! `Symbol`'s thirteen constants have no attribute at all, so
`Symbol.iterator = 1` is the refusal `Math.PI = 1` is. -/

#guard match Heap.initial.readObj symbolCtorRef with
  | some o =>
    o.getOwnProperty "prototype" == some (Property.constant (.obj symbolProtoRef))
      && o.getOwnProperty "for" == some (Property.method (.obj symbolForRef))
      && o.getOwnProperty "keyFor" == some (Property.method (.obj symbolKeyForRef))
      && WellKnownSymbol.all.all fun w =>
           o.getOwnProperty (.str w.name) == some (Property.constant (.sym w.symbol))
  | none => false

/-! `%SymbolRegistry%` is empty, null-prototyped, and bound to no name. -/

#guard match Heap.initial.readObj symbolRegistryRef with
  | some o => o.proto.isNone && o.properties.isEmpty && o.callable.isNone
  | none => false
#guard globalEnv.all fun b =>
  (Heap.initial.read b.2).bind (·.value) != some (.obj symbolRegistryRef)

/-! `JSON` has no `[[Call]]`, and its tag is what makes
`Object.prototype.toString.call(JSON)` `[object JSON]`. -/

#guard match Heap.initial.readObj jsonRef with
  | some o =>
    o.proto == some objectProtoRef
      && o.callable.isNone
      && o.getOwnProperty "parse" == some (Property.method (.obj jsonParseRef))
      && o.getOwnProperty "stringify" == some (Property.method (.obj jsonStringifyRef))
      && o.getOwnProperty WellKnownSymbol.toStringTag.key
        == some (Property.attribute (.prim (.str "JSON")))
  | none => false

/-! The other two `@@toStringTag`s this slice installs. -/

#guard (Heap.initial.readObj mathRef).bind
  (·.getOwnProperty WellKnownSymbol.toStringTag.key)
  == some (Property.attribute (.prim (.str "Math")))

/-! `%Function.prototype[@@hasInstance]%` has no attribute at all
(20.2.3.6), so a script can neither replace nor delete it. -/

#guard (Heap.initial.readObj functionProtoRef).bind
  (·.getOwnProperty WellKnownSymbol.hasInstance.key)
  == some (Property.constant (.obj functionHasInstanceRef))

/-! `AggregateError`'s two links: its `prototype` chains to
`Error.prototype`, and the constructor's own `[[Prototype]]` is `Error`,
as every `NativeError`'s is. -/

#guard match Heap.initial.readObj aggregateErrorProtoRef with
  | some o =>
    o.proto == some ErrorKind.error.protoRef
      && o.callable.isNone
      && o.getOwnProperty "constructor" == some (Property.method (.obj aggregateErrorCtorRef))
      && o.getOwnProperty "name" == some (Property.method (.prim (.str "AggregateError")))
      && o.getOwnProperty "message" == some (Property.method (.prim (.str "")))
  | none => false

#guard (Heap.initial.readObj aggregateErrorCtorRef).bind (·.proto)
  == some ErrorKind.error.ctorRef
#guard match Heap.initial.readObj aggregateErrorCtorRef with
  | some o =>
    (match o.callable with | some (.native .aggregateErrorCtor) => true | _ => false)
      && o.getOwnProperty "length" == some (Property.attribute (Value.ofNat 2))
      && o.getOwnProperty "name" == some (Property.attribute (.prim (.str "AggregateError")))
  | none => false
#guard (Heap.initial.readObj aggregateErrorCtorRef).bind (·.getOwnProperty "prototype")
  == some (Property.constant (.obj aggregateErrorProtoRef))

/-! The two statics this slice hangs off existing constructors. -/

#guard (Heap.initial.readObj objectCtorRef).bind
  (·.getOwnProperty "getOwnPropertySymbols")
  == some (Property.method (.obj objectGetOwnPropertySymbolsRef))
#guard (Heap.initial.readObj ErrorKind.error.ctorRef).bind (·.getOwnProperty "isError")
  == some (Property.method (.obj errorIsErrorRef))
