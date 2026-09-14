import Js.Number.Constants
import Tarski.Value

/-! The realm: the intrinsics a script starts with, at fixed heap
references.

`Heap.initial` is a literal. Every intrinsic's reference is a constant
this file names, so `throwJsError` can allocate an error with the right
prototype without reading the heap to find one, a proof carries the realm
as data `simp` can compute with, and `Test/Tarski/RealmTest.lean` can pin
the literal against the constants so the two cannot drift apart.

| Reference | Intrinsic                                                |
| --------- | -------------------------------------------------------- |
| 0–6       | the seven `Error` prototypes, in `ErrorKind.all`'s order |
| 7–13      | the seven `Error` constructors, in the same order        |
| 14        | `Error.prototype.toString`                               |
| 15        | `Object.prototype`                                       |
| 16        | `Object`                                                 |
| 17–19     | `Object.prototype.hasOwnProperty`, `Object.is`, `Object.keys` |
| 20        | `Array.prototype`                                        |
| 21        | `Array`                                                  |
| 22–24     | `Array.prototype.push`, `Array.prototype.join`, `Array.isArray` |
| 25        | `String`                                                 |
| 26        | `%PrintLog%`, the array `print` appends to                |
| 27        | `print`                                                  |
| 28        | `$262`                                                   |
| 29        | `Number.prototype`, itself a Number object of value `+0` |
| 30        | `Number`                                                 |
| 31–32     | `Number.prototype.toString`, `Number.prototype.valueOf`  |
| 33–36     | `Number.isFinite`, `isInteger`, `isNaN`, `isSafeInteger` |
| 37        | `Boolean.prototype`, itself a Boolean object of value `false` |
| 38        | `Boolean`                                                |
| 39–40     | `Boolean.prototype.toString`, `Boolean.prototype.valueOf` |
| 41        | `Math`                                                   |
| 42–49     | `Math.abs`, `ceil`, `floor`, `fround`, `round`, `sign`, `sqrt`, `trunc` |
| 50–52     | `Math.max`, `Math.min`, `Math.pow`                       |
| 53–54     | `parseFloat`, `parseInt`                                  |
| 55–58     | `Number.prototype.toFixed`, `toExponential`, `toPrecision`, `toLocaleString` |
| 59        | `%ThrowTypeError%`                                       |
| 60        | `console`                                                 |
| 61        | `console.log`                                             |
| 62        | `Function.prototype`, itself callable and answering `undefined` |
| 63        | `Function`                                               |
| 64–67     | `Function.prototype.call`, `apply`, `bind`, `toString`    |
| 68–72     | `Object.prototype.toString`, `valueOf`, `toLocaleString`, `isPrototypeOf`, `propertyIsEnumerable` |
| 73–90     | `Object.assign`, `create`, `defineProperties`, `defineProperty`, `entries`, `freeze`, `getOwnPropertyDescriptor`, `getOwnPropertyDescriptors`, `getOwnPropertyNames`, `getPrototypeOf`, `hasOwn`, `isExtensible`, `isFrozen`, `isSealed`, `preventExtensions`, `seal`, `setPrototypeOf`, `values` |

Ninety-one objects, then, and twenty-one cells. The twenty-one global
bindings are cells 0–20: the seven `Error` constructors, then `Object`,
`Array`, `String`, `print`, `$262`, `Number`, `Boolean`, `Math`, `NaN`,
`Infinity`, `parseFloat`, `parseInt`, `console`, and `Function`.

`parseFloat` and `parseInt` are **one function object each**, bound
globally and read as `Number.parseFloat` and `Number.parseInt`, so
`Number.parseInt === parseInt` is true, as the specification requires.

`Number`, `Boolean`, and `Math` are writable cells like every other
global function binding. `NaN` and `Infinity` are **not**: they are the
specification's non-writable value properties of the global object, so
their cells hold `Js.Number.NaN` and `Js.Number.POSITIVE_INFINITY` with
`mutable := false`, which is what makes `NaN = 1` the same strict-mode
`TypeError` an assignment to a `const` is. A local declaration may still
shadow either name, as it may shadow `Object`.

Every numeric constant on `Number` and on `Math` is the library's own
definition under its source spelling — `Js.Number.EPSILON`,
`Js.Math.PI` — so the realm names the same doubles a `Theorem` does
rather than a second copy of them. `Number.prototype` and
`Boolean.prototype` are themselves wrapper objects, of `+0` and `false`,
as the specification has them: it costs one field each and test262
observes it (`Number.prototype.valueOf()` is `0`). `Math` has no
`[[Call]]` and no `[[Construct]]`, so `Math()` is `not a function`;
`@@toStringTag` on it is #392's. The `String` wrapper object is #391's,
so `String` still has no `prototype` property here.

`print` and `$262` are the two host-defined bindings test262 requires of
an implementation. `print` has no IO to do: it appends ToString of its
argument to `%PrintLog%`, an ordinary intrinsic array, and
`Tarski/Main.lean` writes that log out when the run is over. `$262`'s
hooks — `evalScript`, `createRealm`, `detachArrayBuffer`, `gc`, `agent`,
`global`, `AbstractModuleSource` — are refused by the decoder (see
`Tarski/Decode.lean`), so a test that calls one is *unsupported* rather
than failed; the object itself exists, empty, so that `typeof $262` is
`"object"` and `$262.IsHTMLDDA` reads `undefined`, which is what the
suite asks of a host that does not provide it. There is still no global
*object*: `globalThis`, a top-level `this`, `$262.global`, and
`Object.prototype.__proto__` are #487's, because a global object whose
properties *are* these cells is a change to `Env` and `hoistVars` that no
part of the intrinsics' surface needs.

`console` is not test262's; it is `lakatos exe`'s, the binding an
ordinary program writes its output through. Its `log` appends to the
*same* `%PrintLog%` `print` does, so a run's stdout is one sequence in
program order however the two were mixed, and it holds no other member:
`console.error`, `console.warn`, and the rest are outside #386.

`Object.prototype` carries its whole surface but the two accessors:
`toString`, `valueOf`, `toLocaleString`, `isPrototypeOf`,
`propertyIsEnumerable`, and `hasOwnProperty`, so `{} + 1` is
`"[object Object]1"`. `__proto__` is #487's and `@@toStringTag` is
#392's. Object literals, function `prototype` objects,
`Error.prototype`, and `Array.prototype` all link to it, and
`Object.prototype` itself is null-prototyped.

**Every function object here links to `Function.prototype`**, and so does
every function a script makes: that is what `f.call`, `f.bind`, and
`(function () {}) instanceof Function` all read through.
`Function.prototype` is itself a function — callable, answering
`undefined` whatever it is handed, as 20.2.3 requires — and its own
`[[Prototype]]` is `Object.prototype`. The `Function` constructor exists
as an object because 163 tests reach `Function.prototype` through it;
*calling* it is `eval` by another name and so outside this epic, which
the decoder refuses by name and `callNative` refuses through an alias.

`Array.prototype` is itself an Array exotic object of length 0, as the
spec has it, which is why `Array.isArray(Array.prototype)` is true.

**Every property here carries its specified attributes.** `Obj.builtin`
is the shape 17.1 gives every built-in function — a non-writable,
non-enumerable, non-configurable `length` and `name`, in that order, so
`Object.getOwnPropertyNames(Math.abs)` is `["length", "name"]` — and a
constructor adds its `prototype` (no attribute at all) and its statics
(writable and configurable, never enumerable) after them. A prototype's
`constructor`, an `Error.prototype`'s `name` and `message`, and every
`Math` and `Number` method are the same non-enumerable shape; every
`Math` and `Number` *constant* has no attribute at all, which is what
makes `Math.PI = 1` a strict-mode `TypeError`. The constructors are
`@[reducible]`, so `Heap.initial` is still a literal to `simp`. -/

namespace Tarski

open Js

/-- The kind's `prototype` object: 0–6, in `ErrorKind.all`'s order. -/
def ErrorKind.protoRef : ErrorKind → Ref
  | .error => 0
  | .typeError => 1
  | .rangeError => 2
  | .referenceError => 3
  | .syntaxError => 4
  | .evalError => 5
  | .uriError => 6

/-- The kind's constructor object: 7–13, just past the prototypes. -/
def ErrorKind.ctorRef (k : ErrorKind) : Ref := 7 + k.protoRef

/-- `Error.prototype.toString`, the one intrinsic of the `Error`
hierarchy that is not a constructor or a prototype. -/
def errorToStringRef : Ref := 14

/-- `Object.prototype`: the root of every ordinary prototype chain. -/
def objectProtoRef : Ref := 15

/-- `Object`. -/
def objectCtorRef : Ref := 16

/-- `Object.prototype.hasOwnProperty`. -/
def objectHasOwnPropertyRef : Ref := 17

/-- `Object.is`. -/
def objectIsRef : Ref := 18

/-- `Object.keys`. -/
def objectKeysRef : Ref := 19

/-- `Array.prototype`, itself an array of length 0. -/
def arrayProtoRef : Ref := 20

/-- `Array`. -/
def arrayCtorRef : Ref := 21

/-- `Array.prototype.push`. -/
def arrayPushRef : Ref := 22

/-- `Array.prototype.join`. -/
def arrayJoinRef : Ref := 23

/-- `Array.isArray`. -/
def arrayIsArrayRef : Ref := 24

/-- `String`. It has no `prototype` property yet: the wrapper object and
`String.prototype` are #391's. -/
def stringCtorRef : Ref := 25

/-- `%PrintLog%`, the array `print` appends to. It is an intrinsic with
no binding: the log is realm data the binary reads, not a value a script
can reach. -/
def printLogRef : Ref := 26

/-- `print`, the test262 host's output binding. -/
def printRef : Ref := 27

/-- `$262`, the test262 host object. Empty: its hooks are refused by the
decoder, so nothing here implements one. -/
def hostRef : Ref := 28

/-- `Number.prototype`, itself a Number object whose `[[NumberData]]` is
`+0`. -/
def numberProtoRef : Ref := 29

/-- `Number`. -/
def numberCtorRef : Ref := 30

/-- `Number.prototype.toString`. -/
def numberToStringRef : Ref := 31

/-- `Number.prototype.valueOf`. -/
def numberValueOfRef : Ref := 32

/-- `Number.isFinite`. -/
def numberIsFiniteRef : Ref := 33

/-- `Number.isInteger`. -/
def numberIsIntegerRef : Ref := 34

/-- `Number.isNaN`. -/
def numberIsNaNRef : Ref := 35

/-- `Number.isSafeInteger`. -/
def numberIsSafeIntegerRef : Ref := 36

/-- `Boolean.prototype`, itself a Boolean object whose `[[BooleanData]]`
is `false`. -/
def booleanProtoRef : Ref := 37

/-- `Boolean`. -/
def booleanCtorRef : Ref := 38

/-- `Boolean.prototype.toString`. -/
def booleanToStringRef : Ref := 39

/-- `Boolean.prototype.valueOf`. -/
def booleanValueOfRef : Ref := 40

/-- `Math`. Not a function: it has no `[[Call]]`. -/
def mathRef : Ref := 41

/-- `Math.abs`. -/
def mathAbsRef : Ref := 42

/-- `Math.ceil`. -/
def mathCeilRef : Ref := 43

/-- `Math.floor`. -/
def mathFloorRef : Ref := 44

/-- `Math.fround`. -/
def mathFroundRef : Ref := 45

/-- `Math.round`. -/
def mathRoundRef : Ref := 46

/-- `Math.sign`. -/
def mathSignRef : Ref := 47

/-- `Math.sqrt`. -/
def mathSqrtRef : Ref := 48

/-- `Math.trunc`. -/
def mathTruncRef : Ref := 49

/-- `Math.max`. -/
def mathMaxRef : Ref := 50

/-- `Math.min`. -/
def mathMinRef : Ref := 51

/-- `Math.pow`. -/
def mathPowRef : Ref := 52

/-- `parseFloat`, the one object both the global binding and
`Number.parseFloat` name. -/
def parseFloatRef : Ref := 53

/-- `parseInt`, the one object both the global binding and
`Number.parseInt` name. -/
def parseIntRef : Ref := 54

/-- `Number.prototype.toFixed`. -/
def numberToFixedRef : Ref := 55

/-- `Number.prototype.toExponential`. -/
def numberToExponentialRef : Ref := 56

/-- `Number.prototype.toPrecision`. -/
def numberToPrecisionRef : Ref := 57

/-- `Number.prototype.toLocaleString`. -/
def numberToLocaleStringRef : Ref := 58

/-- `%ThrowTypeError%` (10.2.4.1), the getter and the setter of a strict
`arguments` object's `callee`. One object per realm, as the
specification has it, which is what makes the two halves of that
accessor the same function. It has no global binding: nothing in source
can name it. -/
def throwTypeErrorRef : Ref := 59
/-- `%Function.prototype%`: callable, answering `undefined`, and the
`[[Prototype]]` of every function object in the realm and of every
function a script makes. -/
def functionProtoRef : Ref := 62

/-- `Function`. The object exists; calling it does not (see
`NativeFn.functionCtor`). -/
def functionCtorRef : Ref := 63

/-- `Function.prototype.call`. -/
def functionCallRef : Ref := 64

/-- `Function.prototype.apply`. -/
def functionApplyRef : Ref := 65

/-- `Function.prototype.bind`. -/
def functionBindRef : Ref := 66

/-- `Function.prototype.toString`. -/
def functionToStringRef : Ref := 67

/-- `Object.prototype.toString`. -/
def objectProtoToStringRef : Ref := 68

/-- `Object.prototype.valueOf`. -/
def objectProtoValueOfRef : Ref := 69

/-- `Object.prototype.toLocaleString`. -/
def objectProtoToLocaleStringRef : Ref := 70

/-- `Object.prototype.isPrototypeOf`. -/
def objectProtoIsPrototypeOfRef : Ref := 71

/-- `Object.prototype.propertyIsEnumerable`. -/
def objectProtoPropertyIsEnumerableRef : Ref := 72

/-- `Object.assign`. -/
def objectAssignRef : Ref := 73

/-- `Object.create`. -/
def objectCreateRef : Ref := 74

/-- `Object.defineProperties`. -/
def objectDefinePropertiesRef : Ref := 75

/-- `Object.defineProperty`. -/
def objectDefinePropertyRef : Ref := 76

/-- `Object.entries`. -/
def objectEntriesRef : Ref := 77

/-- `Object.freeze`. -/
def objectFreezeRef : Ref := 78

/-- `Object.getOwnPropertyDescriptor`. -/
def objectGetOwnPropertyDescriptorRef : Ref := 79

/-- `Object.getOwnPropertyDescriptors`. -/
def objectGetOwnPropertyDescriptorsRef : Ref := 80

/-- `Object.getOwnPropertyNames`. -/
def objectGetOwnPropertyNamesRef : Ref := 81

/-- `Object.getPrototypeOf`. -/
def objectGetPrototypeOfRef : Ref := 82

/-- `Object.hasOwn`. -/
def objectHasOwnRef : Ref := 83

/-- `Object.isExtensible`. -/
def objectIsExtensibleRef : Ref := 84

/-- `Object.isFrozen`. -/
def objectIsFrozenRef : Ref := 85

/-- `Object.isSealed`. -/
def objectIsSealedRef : Ref := 86

/-- `Object.preventExtensions`. -/
def objectPreventExtensionsRef : Ref := 87

/-- `Object.seal`. -/
def objectSealRef : Ref := 88

/-- `Object.setPrototypeOf`. -/
def objectSetPrototypeOfRef : Ref := 89

/-- `Object.values`. -/
def objectValuesRef : Ref := 90

/-- A built-in function object with extra own properties after its
`length` and `name`: 17.1's shape, which is what makes
`Object.getOwnPropertyNames(Object)` start `["length", "name",
"prototype"]`. `@[reducible]`, so `Heap.initial` is still a literal to
`simp`. -/
@[reducible] def Obj.builtinWith (f : NativeFn) (name : String) (length : Nat)
    (props : List (String × Property)) : Obj :=
  { proto := some functionProtoRef,
    callable := some (.native f),
    properties :=
      ("length", Property.attribute (Value.ofNat length)) ::
      ("name", Property.attribute (.prim (.str name))) :: props }

/-- A built-in function object with nothing but its `length` and
`name`. -/
@[reducible] def Obj.builtin (f : NativeFn) (name : String) (length : Nat) : Obj :=
  Obj.builtinWith f name length []

/-- `console`, the host object `lakatos exe` writes through. -/
def consoleRef : Ref := 60

/-- `console.log`. -/
def consoleLogRef : Ref := 61

/-- The cell the kind's global binding lives in: 0–6, in the same
order. -/
def ErrorKind.cellRef : ErrorKind → CellRef
  | .error => 0
  | .typeError => 1
  | .rangeError => 2
  | .referenceError => 3
  | .syntaxError => 4
  | .evalError => 5
  | .uriError => 6

/-- The cell `Object` is bound in. -/
def objectCellRef : CellRef := 7

/-- The cell `Array` is bound in. -/
def arrayCellRef : CellRef := 8

/-- The cell `String` is bound in. -/
def stringCellRef : CellRef := 9

/-- The cell `print` is bound in. -/
def printCellRef : CellRef := 10

/-- The cell `$262` is bound in. -/
def hostCellRef : CellRef := 11

/-- The cell `Number` is bound in. -/
def numberCellRef : CellRef := 12

/-- The cell `Boolean` is bound in. -/
def booleanCellRef : CellRef := 13

/-- The cell `Math` is bound in. -/
def mathCellRef : CellRef := 14

/-- The cell `NaN` is bound in. Immutable: the global `NaN` is a
non-writable value property, so assigning to it is a strict-mode
`TypeError`. -/
def nanCellRef : CellRef := 15

/-- The cell `Infinity` is bound in, immutable for the reason `NaN`'s
is. -/
def infinityCellRef : CellRef := 16

/-- The cell `parseFloat` is bound in, writable like every other global
function binding. -/
def parseFloatCellRef : CellRef := 17

/-- The cell `parseInt` is bound in. -/
def parseIntCellRef : CellRef := 18

/-- The cell `console` is bound in, writable like every other global
object binding. -/
def consoleCellRef : CellRef := 19

/-- The cell `Function` is bound in. -/
def functionCellRef : CellRef := 20

/-- The scope a script's own declarations are instantiated on top of:
`ErrorKind.all.map (fun k => (k.name, k.cellRef))`, written out so that
`simp` sees a literal list. There is no global *object* (#487), so a
binding here is an ordinary cell and `globalThis` is absent. -/
def globalEnv : Env :=
  [ ("Error", 0),
    ("TypeError", 1),
    ("RangeError", 2),
    ("ReferenceError", 3),
    ("SyntaxError", 4),
    ("EvalError", 5),
    ("URIError", 6),
    ("Object", 7),
    ("Array", 8),
    ("String", 9),
    ("print", 10),
    ("$262", 11),
    ("Number", 12),
    ("Boolean", 13),
    ("Math", 14),
    ("NaN", 15),
    ("Infinity", 16),
    ("parseFloat", 17),
    ("parseInt", 18),
    ("console", 19),
    ("Function", 20) ]

/-- The heap a script starts from: the realm, laid out at the references
above. -/
def Heap.initial : Heap where
  -- The seven global constructor bindings, cells 0–6. They are writable:
  -- a script may assign to `Error`, as it may to any global function
  -- binding.
  cells :=
    #[ { mutable := true, value := some (.obj 7) },   -- Error
       { mutable := true, value := some (.obj 8) },   -- TypeError
       { mutable := true, value := some (.obj 9) },   -- RangeError
       { mutable := true, value := some (.obj 10) },  -- ReferenceError
       { mutable := true, value := some (.obj 11) },  -- SyntaxError
       { mutable := true, value := some (.obj 12) },  -- EvalError
       { mutable := true, value := some (.obj 13) },  -- URIError
       { mutable := true, value := some (.obj 16) },  -- Object
       { mutable := true, value := some (.obj 21) },  -- Array
       { mutable := true, value := some (.obj 25) },  -- String
       { mutable := true, value := some (.obj 27) },  -- print
       { mutable := true, value := some (.obj 28) },  -- $262
       { mutable := true, value := some (.obj 30) },  -- Number
       { mutable := true, value := some (.obj 38) },  -- Boolean
       { mutable := true, value := some (.obj 41) },  -- Math
       -- `NaN` and `Infinity` are value properties of the global object,
       -- and non-writable ones: immutable cells, so `NaN = 1` throws.
       { mutable := false, value := some (.prim (.num Number.NaN)) },
       { mutable := false,
         value := some (.prim (.num Number.POSITIVE_INFINITY)) },
       { mutable := true, value := some (.obj 53) },  -- parseFloat
       { mutable := true, value := some (.obj 54) },  -- parseInt
       { mutable := true, value := some (.obj 60) },  -- console
       { mutable := true, value := some (.obj 63) } ] -- Function
  objects :=
    #[ -- 0: Error.prototype. `toString` is on it because the binary's
       -- uncaught-error report runs that algorithm anyway. It is an
       -- ordinary object, not an `error` one: `[[ErrorData]]` is on the
       -- instances, so `Object.prototype.toString.call(Error.prototype)`
       -- is `[object Object]`, which is what the suite checks.
       { proto := some 15,
         properties :=
           [ ("constructor", Property.method (.obj 7)),
             ("name", Property.method (.prim (.str "Error"))),
             ("message", Property.method (.prim (.str ""))),
             ("toString", Property.method (.obj 14)) ] },
       -- 1: TypeError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 8)),
             ("name", Property.method (.prim (.str "TypeError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 2: RangeError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 9)),
             ("name", Property.method (.prim (.str "RangeError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 3: ReferenceError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 10)),
             ("name", Property.method (.prim (.str "ReferenceError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 4: SyntaxError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 11)),
             ("name", Property.method (.prim (.str "SyntaxError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 5: EvalError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 12)),
             ("name", Property.method (.prim (.str "EvalError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 6: URIError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 13)),
             ("name", Property.method (.prim (.str "URIError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 7: Error. A subclass constructor's `[[Prototype]]` is `Error`
       -- itself, which is what `TypeError instanceof Error`-shaped
       -- lookups walk; `Error`'s own is `Function.prototype`.
       Obj.builtinWith (.errorCtor .error) "Error" 1
         [("prototype", Property.constant (.obj 0))],
       -- 8: TypeError
       { Obj.builtinWith (.errorCtor .typeError) "TypeError" 1
           [("prototype", Property.constant (.obj 1))] with proto := some 7 },
       -- 9: RangeError
       { Obj.builtinWith (.errorCtor .rangeError) "RangeError" 1
           [("prototype", Property.constant (.obj 2))] with proto := some 7 },
       -- 10: ReferenceError
       { Obj.builtinWith (.errorCtor .referenceError) "ReferenceError" 1
           [("prototype", Property.constant (.obj 3))] with proto := some 7 },
       -- 11: SyntaxError
       { Obj.builtinWith (.errorCtor .syntaxError) "SyntaxError" 1
           [("prototype", Property.constant (.obj 4))] with proto := some 7 },
       -- 12: EvalError
       { Obj.builtinWith (.errorCtor .evalError) "EvalError" 1
           [("prototype", Property.constant (.obj 5))] with proto := some 7 },
       -- 13: URIError
       { Obj.builtinWith (.errorCtor .uriError) "URIError" 1
           [("prototype", Property.constant (.obj 6))] with proto := some 7 },
       -- 14: Error.prototype.toString
       Obj.builtin .errorToString "toString" 0,
       -- 15: Object.prototype. The root of every ordinary chain, and
       -- itself null-prototyped. `__proto__` is #487's and
       -- `@@toStringTag` #392's; the rest of 20.1.3 is here.
       { proto := none,
         properties :=
           [ ("constructor", Property.method (.obj 16)),
             ("hasOwnProperty", Property.method (.obj 17)),
             ("isPrototypeOf", Property.method (.obj 69)),
             ("propertyIsEnumerable", Property.method (.obj 70)),
             ("toLocaleString", Property.method (.obj 68)),
             ("toString", Property.method (.obj 66)),
             ("valueOf", Property.method (.obj 67)) ] },
       -- 16: Object. `fromEntries` and `groupBy` want iterators (#394)
       -- and `getOwnPropertySymbols` wants symbols (#392); everything
       -- else 20.1.2 lists is here.
       Obj.builtinWith .objectCtor "Object" 1
         [ ("prototype", Property.constant (.obj 15)),
           ("assign", Property.method (.obj 71)),
           ("create", Property.method (.obj 72)),
           ("defineProperties", Property.method (.obj 73)),
           ("defineProperty", Property.method (.obj 74)),
           ("entries", Property.method (.obj 75)),
           ("freeze", Property.method (.obj 76)),
           ("getOwnPropertyDescriptor", Property.method (.obj 77)),
           ("getOwnPropertyDescriptors", Property.method (.obj 78)),
           ("getOwnPropertyNames", Property.method (.obj 79)),
           ("getPrototypeOf", Property.method (.obj 80)),
           ("hasOwn", Property.method (.obj 81)),
           ("is", Property.method (.obj 18)),
           ("isExtensible", Property.method (.obj 82)),
           ("isFrozen", Property.method (.obj 83)),
           ("isSealed", Property.method (.obj 84)),
           ("keys", Property.method (.obj 19)),
           ("preventExtensions", Property.method (.obj 85)),
           ("seal", Property.method (.obj 86)),
           ("setPrototypeOf", Property.method (.obj 87)),
           ("values", Property.method (.obj 88)) ],
       -- 17: Object.prototype.hasOwnProperty
       Obj.builtin .objectHasOwnProperty "hasOwnProperty" 1,
       -- 18: Object.is
       Obj.builtin .objectIs "is" 2,
       -- 19: Object.keys
       Obj.builtin .objectKeys "keys" 1,
       -- 20: Array.prototype, an array of length 0.
       { proto := some 15,
         properties :=
           [ ("constructor", Property.method (.obj 21)),
             ("push", Property.method (.obj 22)),
             ("join", Property.method (.obj 23)) ],
         kind := .array 0 true },
       -- 21: Array
       Obj.builtinWith .arrayCtor "Array" 1
         [ ("prototype", Property.constant (.obj 20)),
           ("isArray", Property.method (.obj 24)) ],
       -- 22: Array.prototype.push
       Obj.builtin .arrayPush "push" 1,
       -- 23: Array.prototype.join
       Obj.builtin .arrayJoin "join" 1,
       -- 24: Array.isArray
       Obj.builtin .arrayIsArray "isArray" 1,
       -- 25: String. No `prototype` property: the wrapper is #391's, so
       -- `new String("x")` refuses until then.
       Obj.builtin .stringCtor "String" 1,
       -- 26: %PrintLog%, the array `print` appends to. It is no script's
       -- to reach: nothing binds it, so a run's output is exactly what
       -- `print` put there.
       { proto := some 20, kind := .array 0 true },
       -- 27: print
       Obj.builtin .print "print" 1,
       -- 28: $262. Empty on purpose — its hooks are decoder refusals,
       -- and what is left is an object for `typeof` to see and a missing
       -- `IsHTMLDDA` to read as `undefined`.
       { proto := some 15 },
       -- 29: Number.prototype, itself a Number object of value `+0`, as
       -- the spec has it: `Number.prototype.valueOf()` is `0`.
       { proto := some 15,
         kind := .number 0.0,
         properties :=
           [ ("constructor", Property.method (.obj 30)),
             ("toString", Property.method (.obj 31)),
             ("valueOf", Property.method (.obj 32)),
             ("toFixed", Property.method (.obj 55)),
             ("toExponential", Property.method (.obj 56)),
             ("toPrecision", Property.method (.obj 57)),
             ("toLocaleString", Property.method (.obj 58)) ] },
       -- 30: Number. Every constant is the library's own definition
       -- under its source spelling, and `parseFloat` and `parseInt` are
       -- the same two objects the globals name.
       Obj.builtinWith .numberCtor "Number" 1
         [ ("prototype", Property.constant (.obj 29)),
           ("isFinite", Property.method (.obj 33)),
           ("isInteger", Property.method (.obj 34)),
           ("isNaN", Property.method (.obj 35)),
           ("isSafeInteger", Property.method (.obj 36)),
           ("EPSILON", Property.constant (.prim (.num Number.EPSILON))),
           ("MAX_SAFE_INTEGER", Property.constant (.prim (.num Number.MAX_SAFE_INTEGER))),
           ("MIN_SAFE_INTEGER", Property.constant (.prim (.num Number.MIN_SAFE_INTEGER))),
           ("MAX_VALUE", Property.constant (.prim (.num Number.MAX_VALUE))),
           ("MIN_VALUE", Property.constant (.prim (.num Number.MIN_VALUE))),
           ("POSITIVE_INFINITY", Property.constant (.prim (.num Number.POSITIVE_INFINITY))),
           ("NEGATIVE_INFINITY", Property.constant (.prim (.num Number.NEGATIVE_INFINITY))),
           ("NaN", Property.constant (.prim (.num Number.NaN))),
           ("parseFloat", Property.method (.obj 53)),
           ("parseInt", Property.method (.obj 54)) ],
       -- 31: Number.prototype.toString
       Obj.builtin .numberToString "toString" 1,
       -- 32: Number.prototype.valueOf
       Obj.builtin .numberValueOf "valueOf" 0,
       -- 33: Number.isFinite
       Obj.builtin .numberIsFinite "isFinite" 1,
       -- 34: Number.isInteger
       Obj.builtin .numberIsInteger "isInteger" 1,
       -- 35: Number.isNaN
       Obj.builtin .numberIsNaN "isNaN" 1,
       -- 36: Number.isSafeInteger
       Obj.builtin .numberIsSafeInteger "isSafeInteger" 1,
       -- 37: Boolean.prototype, itself a Boolean object of value
       -- `false`.
       { proto := some 15,
         kind := .boolean false,
         properties :=
           [ ("constructor", Property.method (.obj 38)),
             ("toString", Property.method (.obj 39)),
             ("valueOf", Property.method (.obj 40)) ] },
       -- 38: Boolean
       Obj.builtinWith .booleanCtor "Boolean" 1
         [("prototype", Property.constant (.obj 37))],
       -- 39: Boolean.prototype.toString
       Obj.builtin .booleanToString "toString" 0,
       -- 40: Boolean.prototype.valueOf
       Obj.builtin .booleanValueOf "valueOf" 0,
       -- 41: Math. No `callable`: `Math()` is `not a function` and
       -- `new Math()` is `not a constructor`. The members are exactly
       -- the ones the library expresses — the transcendental family,
       -- `random`, `clz32`, and `imul` are absent rather than faked
       -- (#434 for the first, ToUint32/ToInt32 for the last two). The
       -- eight constants have no attribute at all, so `Math.PI = 1` is
       -- the strict-mode refusal it is in an engine.
       { proto := some 15,
         properties :=
           [ ("E", Property.constant (.prim (.num Math.E))),
             ("LN10", Property.constant (.prim (.num Math.LN10))),
             ("LN2", Property.constant (.prim (.num Math.LN2))),
             ("LOG10E", Property.constant (.prim (.num Math.LOG10E))),
             ("LOG2E", Property.constant (.prim (.num Math.LOG2E))),
             ("PI", Property.constant (.prim (.num Math.PI))),
             ("SQRT1_2", Property.constant (.prim (.num Math.SQRT1_2))),
             ("SQRT2", Property.constant (.prim (.num Math.SQRT2))),
             ("abs", Property.method (.obj 42)),
             ("ceil", Property.method (.obj 43)),
             ("floor", Property.method (.obj 44)),
             ("fround", Property.method (.obj 45)),
             ("round", Property.method (.obj 46)),
             ("sign", Property.method (.obj 47)),
             ("sqrt", Property.method (.obj 48)),
             ("trunc", Property.method (.obj 49)),
             ("max", Property.method (.obj 50)),
             ("min", Property.method (.obj 51)),
             ("pow", Property.method (.obj 52)) ] },
       -- 42: Math.abs
       Obj.builtin .mathAbs "abs" 1,
       -- 43: Math.ceil
       Obj.builtin .mathCeil "ceil" 1,
       -- 44: Math.floor
       Obj.builtin .mathFloor "floor" 1,
       -- 45: Math.fround
       Obj.builtin .mathFround "fround" 1,
       -- 46: Math.round
       Obj.builtin .mathRound "round" 1,
       -- 47: Math.sign
       Obj.builtin .mathSign "sign" 1,
       -- 48: Math.sqrt
       Obj.builtin .mathSqrt "sqrt" 1,
       -- 49: Math.trunc
       Obj.builtin .mathTrunc "trunc" 1,
       -- 50: Math.max
       Obj.builtin .mathMax "max" 2,
       -- 51: Math.min
       Obj.builtin .mathMin "min" 2,
       -- 52: Math.pow
       Obj.builtin .mathPow "pow" 2,
       -- 53: parseFloat, the global and `Number.parseFloat`
       Obj.builtin .parseFloat "parseFloat" 1,
       -- 54: parseInt, the global and `Number.parseInt`
       Obj.builtin .parseInt "parseInt" 2,
       -- 55: Number.prototype.toFixed
       Obj.builtin .numberToFixed "toFixed" 1,
       -- 56: Number.prototype.toExponential
       Obj.builtin .numberToExponential "toExponential" 1,
       -- 57: Number.prototype.toPrecision
       Obj.builtin .numberToPrecision "toPrecision" 1,
       -- 58: Number.prototype.toLocaleString
       Obj.builtin .numberToLocaleString "toLocaleString" 0,
       -- 59: %ThrowTypeError%. The one function whose `name` is not
       -- configurable: 10.2.4.1 makes both its `length` and its `name`
       -- non-writable, non-enumerable, and non-configurable, so a script
       -- that reaches it through `arguments.callee` cannot redefine
       -- either.
       { proto := some 62,
         callable := some (.native .throwTypeError),
         properties :=
           [ ("length", Property.constant (Value.ofNat 0)),
             ("name", Property.constant (.prim (.str ""))) ] },
       -- 60: console, `lakatos exe`'s host binding. `log` and nothing
       -- else; a method like any other, and `log` a built-in like any
       -- other, `Function.prototype`-linked with its `length` and `name`.
       { proto := some 15, properties := [("log", Property.method (.obj 61))] },
       -- 61: console.log
       Obj.builtin .consoleLog "log" 0,
       -- 62: Function.prototype. It is itself a function — 20.2.3 makes
       -- it callable and has it answer `undefined` whatever it is
       -- handed — and it is the only function object whose
       -- `[[Prototype]]` is `Object.prototype` rather than itself. Its
       -- `name` is the empty string, as the spec has it.
       { proto := some 15,
         callable := some (.native .functionProto),
         properties :=
           [ ("length", Property.attribute (Value.ofNat 0)),
             ("name", Property.attribute (.prim (.str ""))),
             ("constructor", Property.method (.obj 63)),
             ("apply", Property.method (.obj 65)),
             ("bind", Property.method (.obj 66)),
             ("call", Property.method (.obj 64)),
             ("toString", Property.method (.obj 67)) ] },
       -- 63: Function. The object is here because every `call`,
       -- `apply`, and `bind` spelling reaches `Function.prototype`
       -- through it and because `isConstructor(Function)` is true;
       -- calling it is the decoder's refusal and, through an alias,
       -- `callNative`'s.
       Obj.builtinWith .functionCtor "Function" 1
         [("prototype", Property.constant (.obj 62))],
       -- 64: Function.prototype.call
       Obj.builtin .functionCall "call" 1,
       -- 65: Function.prototype.apply
       Obj.builtin .functionApply "apply" 2,
       -- 66: Function.prototype.bind
       Obj.builtin .functionBind "bind" 1,
       -- 67: Function.prototype.toString
       Obj.builtin .functionToString "toString" 0,
       -- 68: Object.prototype.toString
       Obj.builtin .objectProtoToString "toString" 0,
       -- 69: Object.prototype.valueOf
       Obj.builtin .objectProtoValueOf "valueOf" 0,
       -- 70: Object.prototype.toLocaleString
       Obj.builtin .objectProtoToLocaleString "toLocaleString" 0,
       -- 71: Object.prototype.isPrototypeOf
       Obj.builtin .objectProtoIsPrototypeOf "isPrototypeOf" 1,
       -- 72: Object.prototype.propertyIsEnumerable
       Obj.builtin .objectProtoPropertyIsEnumerable "propertyIsEnumerable" 1,
       -- 73: Object.assign
       Obj.builtin .objectAssign "assign" 2,
       -- 74: Object.create
       Obj.builtin .objectCreate "create" 2,
       -- 75: Object.defineProperties
       Obj.builtin .objectDefineProperties "defineProperties" 2,
       -- 76: Object.defineProperty
       Obj.builtin .objectDefineProperty "defineProperty" 3,
       -- 77: Object.entries
       Obj.builtin .objectEntries "entries" 1,
       -- 78: Object.freeze
       Obj.builtin .objectFreeze "freeze" 1,
       -- 79: Object.getOwnPropertyDescriptor
       Obj.builtin .objectGetOwnPropertyDescriptor "getOwnPropertyDescriptor" 2,
       -- 80: Object.getOwnPropertyDescriptors
       Obj.builtin .objectGetOwnPropertyDescriptors "getOwnPropertyDescriptors" 1,
       -- 81: Object.getOwnPropertyNames
       Obj.builtin .objectGetOwnPropertyNames "getOwnPropertyNames" 1,
       -- 82: Object.getPrototypeOf
       Obj.builtin .objectGetPrototypeOf "getPrototypeOf" 1,
       -- 83: Object.hasOwn
       Obj.builtin .objectHasOwn "hasOwn" 2,
       -- 84: Object.isExtensible
       Obj.builtin .objectIsExtensible "isExtensible" 1,
       -- 85: Object.isFrozen
       Obj.builtin .objectIsFrozen "isFrozen" 1,
       -- 86: Object.isSealed
       Obj.builtin .objectIsSealed "isSealed" 1,
       -- 87: Object.preventExtensions
       Obj.builtin .objectPreventExtensions "preventExtensions" 1,
       -- 88: Object.seal
       Obj.builtin .objectSeal "seal" 1,
       -- 89: Object.setPrototypeOf
       Obj.builtin .objectSetPrototypeOf "setPrototypeOf" 2,
       -- 90: Object.values
       Obj.builtin .objectValues "values" 1 ]

end Tarski
