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
| 91        | `%TemplateMap%`, the realm's `[[TemplateMap]]`            |
| 92        | `Symbol.prototype`                                       |
| 93        | `Symbol`                                                 |
| 94–95     | `Symbol.for`, `Symbol.keyFor`                            |
| 96–99     | `Symbol.prototype.toString`, `valueOf`, `get description`, `[@@toPrimitive]` |
| 100       | `%SymbolRegistry%`, the registry `Symbol.for` writes      |
| 101       | `JSON`                                                   |
| 102–103   | `JSON.parse`, `JSON.stringify`                           |
| 104–105   | `AggregateError.prototype`, `AggregateError`             |
| 106       | `Function.prototype[@@hasInstance]`                       |
| 107       | `Object.getOwnPropertySymbols`                            |
| 108       | `Error.isError`                                          |
| 109–110   | `%IteratorPrototype%`, `%IteratorPrototype%[@@iterator]` |
| 111–112   | `%ArrayIteratorPrototype%`, its `next`                    |
| 113–115   | `Array.prototype.keys`, `values`, `entries`               |
| 116–117   | `Object.fromEntries`, `Object.groupBy`                    |

| 109       | `String.prototype`, itself a String object of `""`        |
| 110–112   | `String.fromCharCode`, `String.fromCodePoint`, `String.raw` |
| 113–143   | `String.prototype.at`, `charAt`, `charCodeAt`, `codePointAt`, `concat`, `endsWith`, `includes`, `indexOf`, `isWellFormed`, `lastIndexOf`, `localeCompare`, `normalize`, `padEnd`, `padStart`, `repeat`, `replace`, `replaceAll`, `slice`, `split`, `startsWith`, `substring`, `toLocaleLowerCase`, `toLocaleUpperCase`, `toLowerCase`, `toString`, `toUpperCase`, `toWellFormed`, `trim`, `trimEnd`, `trimStart`, `valueOf` |
| 144–145   | `%IteratorPrototype%`, `%IteratorPrototype%[@@iterator]` |
| 146–147   | `%ArrayIteratorPrototype%`, its `next`                    |
| 148–150   | `Array.prototype.keys`, `values`, `entries`               |
| 151–152   | `Object.fromEntries`, `Object.groupBy`                    |
| 153–154   | `%StringIteratorPrototype%`, its `next`                   |
| 155       | `String.prototype[@@iterator]`                            |

A hundred and fifty-six objects, then, and thirty-seven cells. The
twenty-four global bindings are cells 0–23: the seven `Error`
constructors, then `Object`, `Array`, `String`, `print`, `$262`,
`Number`, `Boolean`, `Math`, `NaN`, `Infinity`, `parseFloat`,
`parseInt`, `console`, `Function`, `Symbol`, `JSON`, and
`AggregateError`. Cells 24–36 are bound to no name at all: they are the
thirteen **well-known symbols' identities**, allocated so that
`Symbol.iterator` is one fixed symbol per realm and so that a symbol's
identity is a cell here exactly as a `Symbol()` call's is. They are
immutable and empty and are never read.

`Symbol` is the third primitive (`Tarski/Value.lean`), and the thirteen
well-known symbols are *values* here: `@@toPrimitive`, `@@toStringTag`,
`@@hasInstance`, and `@@iterator` have their semantics in the evaluator,
and the other nine wait for the protocols that read them (#390's
`Array.prototype`).

`%IteratorPrototype%` and `%ArrayIteratorPrototype%` are **unbound
intrinsics**: nothing in source names either one — `Iterator`, the
constructor, is outside this epic — and they are reached only through
`[].values()` and `Object.getPrototypeOf`. `%IteratorPrototype%`'s
`@@iterator` answers its own receiver, which is what makes every
iterator that inherits from it iterable; `%ArrayIteratorPrototype%`'s
`@@toStringTag` is `"Array Iterator"`, which is where
`[object Array Iterator]` comes from, there being no `builtinTag` row
for it. `Array.prototype[@@iterator]` *is* `Array.prototype.values`
(23.1.3.40) — one object, not two — and an `arguments` object's
`@@iterator` is that same object (10.4.4.6 step 8). `%SymbolRegistry%` is an intrinsic with no binding,
like `%PrintLog%`: `Symbol.for`'s string keys to its symbols, which is
what makes `Symbol.for("q") === Symbol.for("q")`.

`JSON` is an ordinary object with no `[[Call]]`, so `JSON()` is `not a
function`; its grammar and its serializer are `Tarski/Json.lean` and
`Tarski/Eval.lean`'s `callJsonNative`. `AggregateError` is a native of
its own rather than an eighth `ErrorKind`: `ErrorKind` is the set the
evaluator itself throws, and its order fixes references 0–13 and cells
0–6.

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
`[[Call]]` and no `[[Construct]]`, so `Math()` is `not a function`, and
its `@@toStringTag` is `"Math"`. `String.prototype` is itself a String
exotic object of the empty string, as 22.1.3 has it, so
`Object.prototype.toString.call(String.prototype)` is `[object String]`;
every one of its methods is generic — RequireObjectCoercible then
ToString — but `toString` and `valueOf`, which want a String primitive or
a String object.

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
`"[object Object]1"`. `__proto__` is #487's; `Object.prototype` has no
`@@toStringTag` of its own — the tag is `Object.prototype.toString`'s
own read of one. Object literals, function `prototype` objects,
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
non-enumerable, configurable `length` and `name`, in that order, so
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

/-- `String`, the constructor: a converter when it is called and the
wrapper object when it is `new`ed. -/
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

/-- `Symbol.prototype`. -/
def symbolProtoRef : Ref := 92

/-- `Symbol`. -/
def symbolCtorRef : Ref := 93

/-- `Symbol.for`. -/
def symbolForRef : Ref := 94

/-- `Symbol.keyFor`. -/
def symbolKeyForRef : Ref := 95

/-- `Symbol.prototype.toString`. -/
def symbolProtoToStringRef : Ref := 96

/-- `Symbol.prototype.valueOf`. -/
def symbolProtoValueOfRef : Ref := 97

/-- `get Symbol.prototype.description`. -/
def symbolDescriptionRef : Ref := 98

/-- `Symbol.prototype[@@toPrimitive]`. -/
def symbolToPrimitiveRef : Ref := 99

/-- `%SymbolRegistry%`, the GlobalSymbolRegistry (20.4.2.2's table) as an
object: `Symbol.for`'s string keys to the symbols it has handed out. It
is null-prototyped and bound to no name, so nothing a script does can
reach it or shadow one of its keys. -/
def symbolRegistryRef : Ref := 100

/-- `JSON`. -/
def jsonRef : Ref := 101

/-- `JSON.parse`. -/
def jsonParseRef : Ref := 102

/-- `JSON.stringify`. -/
def jsonStringifyRef : Ref := 103

/-- `AggregateError.prototype`. -/
def aggregateErrorProtoRef : Ref := 104

/-- `AggregateError`. -/
def aggregateErrorCtorRef : Ref := 105

/-- `Function.prototype[@@hasInstance]`. -/
def functionHasInstanceRef : Ref := 106

/-- `Object.getOwnPropertySymbols`. -/
def objectGetOwnPropertySymbolsRef : Ref := 107

/-- `Error.isError`. -/
def errorIsErrorRef : Ref := 108

/-- `%IteratorPrototype%` (27.1.2), which every iterator here inherits
from and which nothing in source can name. -/
def iteratorProtoRef : Ref := 144

/-- `%IteratorPrototype%[@@iterator]` (27.1.2.1). -/
def iteratorProtoIteratorRef : Ref := 145

/-- `%ArrayIteratorPrototype%` (23.1.5.2). -/
def arrayIteratorProtoRef : Ref := 146

/-- `%ArrayIteratorPrototype%.next` (23.1.5.2.1). -/
def arrayIteratorNextRef : Ref := 147

/-- `Array.prototype.keys`. -/
def arrayKeysRef : Ref := 148

/-- `Array.prototype.values`, which is `Array.prototype[@@iterator]` and
an `arguments` object's `@@iterator` too. -/
def arrayValuesRef : Ref := 149

/-- `Array.prototype.entries`. -/
def arrayEntriesRef : Ref := 150

/-- `Object.fromEntries`. -/
def objectFromEntriesRef : Ref := 151

/-- `Object.groupBy`. -/
def objectGroupByRef : Ref := 152

/-- `%StringIteratorPrototype%` (22.1.5.1). -/
def stringIteratorProtoRef : Ref := 153

/-- `%StringIteratorPrototype%.next` (22.1.5.1.1). -/
def stringIteratorNextRef : Ref := 154

/-- `String.prototype[@@iterator]` (22.1.3.36). -/
def stringProtoIteratorRef : Ref := 155

/-- The cell the first well-known symbol's identity lives in; the
thirteen run from here to 36, in 6.1.5.1's table order. -/
def wellKnownSymbolCellBase : CellRef := 24

/-- The thirteen well-known symbols (6.1.5.1), in the table's order.
They are *values* in this slice: `@@toPrimitive`, `@@toStringTag`, and
`@@hasInstance` have their semantics in the evaluator, and the rest wait
for the protocols that read them. `Symbol.dispose` and
`Symbol.asyncDispose` are absent with the rest of explicit resource
management. -/
inductive WellKnownSymbol where
  | asyncIterator
  | hasInstance
  | isConcatSpreadable
  | iterator
  | «match»
  | matchAll
  | replace
  | search
  | species
  | split
  | toPrimitive
  | toStringTag
  | unscopables
deriving Repr, DecidableEq, Inhabited

/-- The symbol's spelling as a property of `Symbol`. -/
def WellKnownSymbol.name : WellKnownSymbol → String
  | .asyncIterator => "asyncIterator"
  | .hasInstance => "hasInstance"
  | .isConcatSpreadable => "isConcatSpreadable"
  | .iterator => "iterator"
  | .«match» => "match"
  | .matchAll => "matchAll"
  | .replace => "replace"
  | .search => "search"
  | .species => "species"
  | .split => "split"
  | .toPrimitive => "toPrimitive"
  | .toStringTag => "toStringTag"
  | .unscopables => "unscopables"

/-- Its `[[Description]]`, which is its name with `Symbol.` in front. -/
def WellKnownSymbol.description (w : WellKnownSymbol) : String :=
  "Symbol." ++ w.name

/-- Its identity: a fixed cell, one per symbol, so that a well-known
symbol is a literal `simp` can compute with. -/
def WellKnownSymbol.id : WellKnownSymbol → SymbolId
  | .asyncIterator => 24
  | .hasInstance => 25
  | .isConcatSpreadable => 26
  | .iterator => 27
  | .«match» => 28
  | .matchAll => 29
  | .replace => 30
  | .search => 31
  | .species => 32
  | .split => 33
  | .toPrimitive => 34
  | .toStringTag => 35
  | .unscopables => 36

/-- The symbol itself. -/
def WellKnownSymbol.symbol (w : WellKnownSymbol) : Symbol :=
  { id := w.id, description := some w.description }

/-- The symbol as a property key. -/
def WellKnownSymbol.key (w : WellKnownSymbol) : Key :=
  .sym w.symbol

/-- Every well-known symbol, in the table's order. -/
def WellKnownSymbol.all : List WellKnownSymbol :=
  [ .asyncIterator, .hasInstance, .isConcatSpreadable, .iterator, .«match», .matchAll,
    .replace, .search, .species, .split, .toPrimitive, .toStringTag, .unscopables ]

/-- A built-in function object with extra own properties after its
`length` and `name`: 17.1's shape, which is what makes
`Object.getOwnPropertyNames(Object)` start `["length", "name",
"prototype"]`. `@[reducible]`, so `Heap.initial` is still a literal to
`simp`. -/
@[reducible] def Obj.builtinWith (f : NativeFn) (name : String) (length : Nat)
    (props : List (Key × Property)) : Obj :=
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

/-- `%TemplateMap%`, the realm's `[[TemplateMap]]` (9.3): the per-realm
registry GetTemplateObject caches template objects in, as an object whose
own keys are the decoder's site numbers and whose values are the template
objects. It has no global binding — nothing in source can name it, as
nothing can name `%ThrowTypeError%` — and it is an object rather than a
field of `Heap` because the heap's shape is a value-domain decision this
slice does not reopen. -/
def templateMapRef : Ref := 91

/-- `String.prototype`, itself a String object whose `[[StringData]]` is
the empty string, as 22.1.3 has it — so
`Object.prototype.toString.call(String.prototype)` is `[object String]`
and `String.prototype.length` is `0`. -/
def stringProtoRef : Ref := 109

/-- Each `String` member's object: the three statics at 93–95 and
`String.prototype`'s thirty-one methods at 96–126, in `StringFn.all`'s
order. Written as a match rather than as an index into `StringFn.all`, so
that every reference is a literal to `simp`. -/
def StringFn.ref : StringFn → Ref
  | .fromCharCode => 110
  | .fromCodePoint => 111
  | .raw => 112
  | .at => 113
  | .charAt => 114
  | .charCodeAt => 115
  | .codePointAt => 116
  | .concat => 117
  | .endsWith => 118
  | .includes => 119
  | .indexOf => 120
  | .isWellFormed => 121
  | .lastIndexOf => 122
  | .localeCompare => 123
  | .normalize => 124
  | .padEnd => 125
  | .padStart => 126
  | .«repeat» => 127
  | .replace => 128
  | .replaceAll => 129
  | .slice => 130
  | .split => 131
  | .startsWith => 132
  | .substring => 133
  | .toLocaleLowerCase => 134
  | .toLocaleUpperCase => 135
  | .toLowerCase => 136
  | .«toString» => 137
  | .«toUpperCase» => 138
  | .toWellFormed => 139
  | .trim => 140
  | .trimEnd => 141
  | .trimStart => 142
  | .valueOf => 143

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

/-- The cell `Symbol` is bound in. -/
def symbolCellRef : CellRef := 21

/-- The cell `JSON` is bound in. -/
def jsonCellRef : CellRef := 22

/-- The cell `AggregateError` is bound in. -/
def aggregateErrorCellRef : CellRef := 23

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
    ("Function", 20),
    ("Symbol", 21),
    ("JSON", 22),
    ("AggregateError", 23) ]

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
       { mutable := true, value := some (.obj 63) },  -- Function
       { mutable := true, value := some (.obj 93) },  -- Symbol
       { mutable := true, value := some (.obj 101) }, -- JSON
       { mutable := true, value := some (.obj 105) }, -- AggregateError
       -- 24–36: the thirteen well-known symbols' identities, in
       -- 6.1.5.1's order. A symbol's identity *is* a cell, so these are
       -- allocated like any other; nothing ever reads or writes one.
       { mutable := false, value := none },           -- Symbol.asyncIterator
       { mutable := false, value := none },           -- Symbol.hasInstance
       { mutable := false, value := none },           -- Symbol.isConcatSpreadable
       { mutable := false, value := none },           -- Symbol.iterator
       { mutable := false, value := none },           -- Symbol.match
       { mutable := false, value := none },           -- Symbol.matchAll
       { mutable := false, value := none },           -- Symbol.replace
       { mutable := false, value := none },           -- Symbol.search
       { mutable := false, value := none },           -- Symbol.species
       { mutable := false, value := none },           -- Symbol.split
       { mutable := false, value := none },           -- Symbol.toPrimitive
       { mutable := false, value := none },           -- Symbol.toStringTag
       { mutable := false, value := none } ]          -- Symbol.unscopables
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
         [ ("prototype", Property.constant (.obj 0)),
           ("isError", Property.method (.obj 108)) ],
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
       -- itself null-prototyped. `__proto__` is #487's; the rest of
       -- 20.1.3 is here.
       { proto := none,
         properties :=
           [ ("constructor", Property.method (.obj 16)),
             ("hasOwnProperty", Property.method (.obj 17)),
             ("isPrototypeOf", Property.method (.obj 71)),
             ("propertyIsEnumerable", Property.method (.obj 72)),
             ("toLocaleString", Property.method (.obj 70)),
             ("toString", Property.method (.obj 68)),
             ("valueOf", Property.method (.obj 69)) ] },
       -- 16: Object, the whole of 20.1.2.
       Obj.builtinWith .objectCtor "Object" 1
         [ ("prototype", Property.constant (.obj 15)),
           ("assign", Property.method (.obj 73)),
           ("create", Property.method (.obj 74)),
           ("defineProperties", Property.method (.obj 75)),
           ("defineProperty", Property.method (.obj 76)),
           ("entries", Property.method (.obj 77)),
           ("freeze", Property.method (.obj 78)),
           ("fromEntries", Property.method (.obj 151)),
           ("getOwnPropertyDescriptor", Property.method (.obj 79)),
           ("getOwnPropertyDescriptors", Property.method (.obj 80)),
           ("getOwnPropertyNames", Property.method (.obj 81)),
           ("getOwnPropertySymbols", Property.method (.obj 107)),
           ("getPrototypeOf", Property.method (.obj 82)),
           ("groupBy", Property.method (.obj 152)),
           ("hasOwn", Property.method (.obj 83)),
           ("is", Property.method (.obj 18)),
           ("isExtensible", Property.method (.obj 84)),
           ("isFrozen", Property.method (.obj 85)),
           ("isSealed", Property.method (.obj 86)),
           ("keys", Property.method (.obj 19)),
           ("preventExtensions", Property.method (.obj 87)),
           ("seal", Property.method (.obj 88)),
           ("setPrototypeOf", Property.method (.obj 89)),
           ("values", Property.method (.obj 90)) ],
       -- 17: Object.prototype.hasOwnProperty
       Obj.builtin .objectHasOwnProperty "hasOwnProperty" 1,
       -- 18: Object.is
       Obj.builtin .objectIs "is" 2,
       -- 19: Object.keys
       Obj.builtin .objectKeys "keys" 1,
       -- 20: Array.prototype, an array of length 0. The members are in
       -- 23.1.3's own order, and `@@iterator` is `values` itself
       -- (23.1.3.40) rather than a second function object.
       { proto := some 15,
         properties :=
           [ ("constructor", Property.method (.obj 21)),
             ("entries", Property.method (.obj 150)),
             ("join", Property.method (.obj 23)),
             ("keys", Property.method (.obj 148)),
             ("push", Property.method (.obj 22)),
             ("values", Property.method (.obj 149)),
             (WellKnownSymbol.iterator.key, Property.method (.obj 149)) ],
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
       -- 25: String, with its `prototype` and its three statics.
       Obj.builtinWith .stringCtor "String" 1
         [ ("prototype", Property.constant (.obj 109)),
           ("fromCharCode", Property.method (.obj 110)),
           ("fromCodePoint", Property.method (.obj 111)),
           ("raw", Property.method (.obj 112)) ],
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
             ("pow", Property.method (.obj 52)),
             (WellKnownSymbol.toStringTag.key,
               Property.attribute (.prim (.str "Math"))) ] },
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
             ("toString", Property.method (.obj 67)),
             -- 20.2.3.6: no attribute at all, so a script can neither
             -- replace nor delete the intrinsic handler.
             (WellKnownSymbol.hasInstance.key, Property.constant (.obj 106)) ] },
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
       Obj.builtin .objectValues "values" 1,
       -- 91: %TemplateMap%, which starts empty and is only ever written
       -- to by GetTemplateObject.
       { },
       -- 92: Symbol.prototype. An ordinary object, not a Symbol one:
       -- `[[SymbolData]]` is on the wrappers, so
       -- `Object.prototype.toString.call(Symbol.prototype)` reads the
       -- `@@toStringTag` here and answers `[object Symbol]` for that
       -- reason rather than for a slot's.
       { proto := some 15,
         properties :=
           [ ("constructor", Property.method (.obj 93)),
             ("toString", Property.method (.obj 96)),
             ("valueOf", Property.method (.obj 97)),
             ("description",
               { slot := .accessor { getter := some (.obj 98) },
                 enumerable := false, configurable := true }),
             (WellKnownSymbol.toPrimitive.key, Property.attribute (.obj 99)),
             (WellKnownSymbol.toStringTag.key,
               Property.attribute (.prim (.str "Symbol"))) ] },
       -- 93: Symbol. Its thirteen well-known members have no attribute
       -- at all (20.4.2), so `Symbol.iterator = 1` is the strict-mode
       -- refusal an assignment to `Math.PI` is.
       Obj.builtinWith .symbolCtor "Symbol" 0
         [ ("prototype", Property.constant (.obj 92)),
           ("for", Property.method (.obj 94)),
           ("keyFor", Property.method (.obj 95)),
           ("asyncIterator", Property.constant (.sym WellKnownSymbol.asyncIterator.symbol)),
           ("hasInstance", Property.constant (.sym WellKnownSymbol.hasInstance.symbol)),
           ("isConcatSpreadable",
             Property.constant (.sym WellKnownSymbol.isConcatSpreadable.symbol)),
           ("iterator", Property.constant (.sym WellKnownSymbol.iterator.symbol)),
           ("match", Property.constant (.sym WellKnownSymbol.«match».symbol)),
           ("matchAll", Property.constant (.sym WellKnownSymbol.matchAll.symbol)),
           ("replace", Property.constant (.sym WellKnownSymbol.replace.symbol)),
           ("search", Property.constant (.sym WellKnownSymbol.search.symbol)),
           ("species", Property.constant (.sym WellKnownSymbol.species.symbol)),
           ("split", Property.constant (.sym WellKnownSymbol.split.symbol)),
           ("toPrimitive", Property.constant (.sym WellKnownSymbol.toPrimitive.symbol)),
           ("toStringTag", Property.constant (.sym WellKnownSymbol.toStringTag.symbol)),
           ("unscopables", Property.constant (.sym WellKnownSymbol.unscopables.symbol)) ],
       -- 94: Symbol.for
       Obj.builtin .symbolFor "for" 1,
       -- 95: Symbol.keyFor
       Obj.builtin .symbolKeyFor "keyFor" 1,
       -- 96: Symbol.prototype.toString
       Obj.builtin .symbolProtoToString "toString" 0,
       -- 97: Symbol.prototype.valueOf
       Obj.builtin .symbolProtoValueOf "valueOf" 0,
       -- 98: get Symbol.prototype.description. A getter's `name` is
       -- `"get "` and the property's spelling (10.2.9).
       Obj.builtin .symbolDescription "get description" 0,
       -- 99: Symbol.prototype[@@toPrimitive]. A symbol-keyed method's
       -- `name` is its key's description in brackets (10.2.9).
       Obj.builtin .symbolToPrimitive "[Symbol.toPrimitive]" 1,
       -- 100: %SymbolRegistry%. Null-prototyped, so a key of `Symbol.for`
       -- can never collide with an inherited one.
       { proto := none },
       -- 101: JSON. Ordinary, with no `[[Call]]`, so `JSON()` is `not a
       -- function`; the tag is what makes
       -- `Object.prototype.toString.call(JSON)` `[object JSON]`.
       { proto := some 15,
         properties :=
           [ ("parse", Property.method (.obj 102)),
             ("stringify", Property.method (.obj 103)),
             (WellKnownSymbol.toStringTag.key,
               Property.attribute (.prim (.str "JSON"))) ] },
       -- 102: JSON.parse
       Obj.builtin .jsonParse "parse" 2,
       -- 103: JSON.stringify
       Obj.builtin .jsonStringify "stringify" 3,
       -- 104: AggregateError.prototype
       { proto := some 0,
         properties :=
           [ ("constructor", Property.method (.obj 105)),
             ("name", Property.method (.prim (.str "AggregateError"))),
             ("message", Property.method (.prim (.str ""))) ] },
       -- 105: AggregateError. Its `[[Prototype]]` is `Error` itself, as
       -- every `NativeError`'s is.
       { Obj.builtinWith .aggregateErrorCtor "AggregateError" 2
           [("prototype", Property.constant (.obj 104))] with proto := some 7 },
       -- 106: Function.prototype[@@hasInstance]
       Obj.builtin .functionHasInstance "[Symbol.hasInstance]" 1,
       -- 107: Object.getOwnPropertySymbols
       Obj.builtin .objectGetOwnPropertySymbols "getOwnPropertySymbols" 1,
       -- 108: Error.isError
       Obj.builtin .errorIsError "isError" 1,
       -- 109: String.prototype. It is itself a String exotic object whose
       -- `[[StringData]]` is the empty string, as 22.1.3 has it and as
       -- `Number.prototype` and `Boolean.prototype` already are here, so
       -- `Object.prototype.toString.call(String.prototype)` answers
       -- `[object String]` and `String.prototype.length` is `0`. Every
       -- method on it but `toString` and `valueOf` is generic. The keys
       -- are spelled `Key.str` because the list is thirty-three long: past
       -- thirty-two elements Lean elaborates a list literal in chunks and
       -- the `String → Key` coercion no longer reaches the tail.
       { proto := some 15,
         kind := .string (Js.JsString.ofString ""),
         properties :=
           [ (Key.str "length", Property.constant (Value.ofNat 0)),
             (Key.str "constructor", Property.method (.obj 25)),
             (Key.str "at", Property.method (.obj 113)),
             (Key.str "charAt", Property.method (.obj 114)),
             (Key.str "charCodeAt", Property.method (.obj 115)),
             (Key.str "codePointAt", Property.method (.obj 116)),
             (Key.str "concat", Property.method (.obj 117)),
             (Key.str "endsWith", Property.method (.obj 118)),
             (Key.str "includes", Property.method (.obj 119)),
             (Key.str "indexOf", Property.method (.obj 120)),
             (Key.str "isWellFormed", Property.method (.obj 121)),
             (Key.str "lastIndexOf", Property.method (.obj 122)),
             (Key.str "localeCompare", Property.method (.obj 123)),
             (Key.str "normalize", Property.method (.obj 124)),
             (Key.str "padEnd", Property.method (.obj 125)),
             (Key.str "padStart", Property.method (.obj 126)),
             (Key.str "repeat", Property.method (.obj 127)),
             (Key.str "replace", Property.method (.obj 128)),
             (Key.str "replaceAll", Property.method (.obj 129)),
             (Key.str "slice", Property.method (.obj 130)),
             (Key.str "split", Property.method (.obj 131)),
             (Key.str "startsWith", Property.method (.obj 132)),
             (Key.str "substring", Property.method (.obj 133)),
             (Key.str "toLocaleLowerCase", Property.method (.obj 134)),
             (Key.str "toLocaleUpperCase", Property.method (.obj 135)),
             (Key.str "toLowerCase", Property.method (.obj 136)),
             (Key.str "toString", Property.method (.obj 137)),
             (Key.str "toUpperCase", Property.method (.obj 138)),
             (Key.str "toWellFormed", Property.method (.obj 139)),
             (Key.str "trim", Property.method (.obj 140)),
             (Key.str "trimEnd", Property.method (.obj 141)),
             (Key.str "trimStart", Property.method (.obj 142)),
             (Key.str "valueOf", Property.method (.obj 143)),
             (WellKnownSymbol.iterator.key, Property.method (.obj 155)) ] },
       -- 110: String.fromCharCode
       Obj.builtin (.string .fromCharCode) "fromCharCode" 1,
       -- 111: String.fromCodePoint
       Obj.builtin (.string .fromCodePoint) "fromCodePoint" 1,
       -- 112: String.raw
       Obj.builtin (.string .raw) "raw" 1,
       -- 113: String.prototype.at
       Obj.builtin (.string .at) "at" 1,
       -- 114: String.prototype.charAt
       Obj.builtin (.string .charAt) "charAt" 1,
       -- 115: String.prototype.charCodeAt
       Obj.builtin (.string .charCodeAt) "charCodeAt" 1,
       -- 116: String.prototype.codePointAt
       Obj.builtin (.string .codePointAt) "codePointAt" 1,
       -- 117: String.prototype.concat
       Obj.builtin (.string .concat) "concat" 1,
       -- 118: String.prototype.endsWith
       Obj.builtin (.string .endsWith) "endsWith" 1,
       -- 119: String.prototype.includes
       Obj.builtin (.string .includes) "includes" 1,
       -- 120: String.prototype.indexOf
       Obj.builtin (.string .indexOf) "indexOf" 1,
       -- 121: String.prototype.isWellFormed
       Obj.builtin (.string .isWellFormed) "isWellFormed" 0,
       -- 122: String.prototype.lastIndexOf
       Obj.builtin (.string .lastIndexOf) "lastIndexOf" 1,
       -- 123: String.prototype.localeCompare
       Obj.builtin (.string .localeCompare) "localeCompare" 1,
       -- 124: String.prototype.normalize
       Obj.builtin (.string .normalize) "normalize" 0,
       -- 125: String.prototype.padEnd
       Obj.builtin (.string .padEnd) "padEnd" 1,
       -- 126: String.prototype.padStart
       Obj.builtin (.string .padStart) "padStart" 1,
       -- 127: String.prototype.repeat
       Obj.builtin (.string .«repeat») "repeat" 1,
       -- 128: String.prototype.replace
       Obj.builtin (.string .replace) "replace" 2,
       -- 129: String.prototype.replaceAll
       Obj.builtin (.string .replaceAll) "replaceAll" 2,
       -- 130: String.prototype.slice
       Obj.builtin (.string .slice) "slice" 2,
       -- 131: String.prototype.split
       Obj.builtin (.string .split) "split" 2,
       -- 132: String.prototype.startsWith
       Obj.builtin (.string .startsWith) "startsWith" 1,
       -- 133: String.prototype.substring
       Obj.builtin (.string .substring) "substring" 2,
       -- 134: String.prototype.toLocaleLowerCase
       Obj.builtin (.string .toLocaleLowerCase) "toLocaleLowerCase" 0,
       -- 135: String.prototype.toLocaleUpperCase
       Obj.builtin (.string .toLocaleUpperCase) "toLocaleUpperCase" 0,
       -- 136: String.prototype.toLowerCase
       Obj.builtin (.string .toLowerCase) "toLowerCase" 0,
       -- 137: String.prototype.toString
       Obj.builtin (.string .«toString») "toString" 0,
       -- 138: String.prototype.toUpperCase
       Obj.builtin (.string .«toUpperCase») "toUpperCase" 0,
       -- 139: String.prototype.toWellFormed
       Obj.builtin (.string .toWellFormed) "toWellFormed" 0,
       -- 140: String.prototype.trim
       Obj.builtin (.string .trim) "trim" 0,
       -- 141: String.prototype.trimEnd
       Obj.builtin (.string .trimEnd) "trimEnd" 0,
       -- 142: String.prototype.trimStart
       Obj.builtin (.string .trimStart) "trimStart" 0,
       -- 143: String.prototype.valueOf
       Obj.builtin (.string .valueOf) "valueOf" 0,
       -- 144: %IteratorPrototype%. Unbound: nothing in source names it.
       { proto := some 15,
         properties :=
           [ (WellKnownSymbol.iterator.key, Property.method (.obj 145)) ] },
       -- 145: %IteratorPrototype%[@@iterator], which answers its own
       -- receiver.
       Obj.builtin .iteratorProtoIterator "[Symbol.iterator]" 0,
       -- 146: %ArrayIteratorPrototype%. Its tag is what makes
       -- `Object.prototype.toString.call([].values())` answer
       -- `[object Array Iterator]`.
       { proto := some 144,
         properties :=
           [ ("next", Property.method (.obj 147)),
             (WellKnownSymbol.toStringTag.key,
               Property.attribute (.prim (.str "Array Iterator"))) ] },
       -- 147: %ArrayIteratorPrototype%.next
       Obj.builtin .arrayIteratorNext "next" 0,
       -- 148: Array.prototype.keys
       Obj.builtin .arrayKeys "keys" 0,
       -- 149: Array.prototype.values, which Array.prototype[@@iterator]
       -- and an `arguments` object's `@@iterator` both are.
       Obj.builtin .arrayValues "values" 0,
       -- 150: Array.prototype.entries
       Obj.builtin .arrayEntries "entries" 0,
       -- 151: Object.fromEntries
       Obj.builtin .objectFromEntries "fromEntries" 1,
       -- 152: Object.groupBy
       Obj.builtin .objectGroupBy "groupBy" 2,
       -- 153: %StringIteratorPrototype%, which walks a string by *code
       -- point* rather than by code unit — the one place the two differ
       -- observably outside `codePointAt`.
       { proto := some 144,
         properties :=
           [ ("next", Property.method (.obj 154)),
             (WellKnownSymbol.toStringTag.key,
               Property.attribute (.prim (.str "String Iterator"))) ] },
       -- 154: %StringIteratorPrototype%.next
       Obj.builtin .stringIteratorNext "next" 0,
       -- 155: String.prototype[@@iterator]
       Obj.builtin .stringProtoIterator "[Symbol.iterator]" 0 ]

end Tarski
