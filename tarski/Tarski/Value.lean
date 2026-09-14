import Js.Val
import Tarski.Ast

/-! The value domain, the heap, environments, and completions.

Bindings live in the heap, not in the environment, for two reasons: an
assignment inside a `while` body must be visible after the loop, and a
closure captures an `Env` by value while still seeing later writes to the
cells it names. A closure is therefore a list of names paired with cell
references, and two closures over the same block share the same cells.

A cell's value is optional, and `none` is the temporal dead zone: block
instantiation allocates every `let`, `const`, and function declaration's
cell before the block's first statement runs, so a name is in scope
before its declarator is reached and reading it there is a
`ReferenceError` rather than `undefined`. -/

namespace Tarski

open Js

-- The library derives `Repr` on `JsVal` but not `DecidableEq`, having no
-- use for it; the evaluator's tests compare whole results, so derive it
-- here rather than give the library an instance it does not need.
deriving instance DecidableEq for JsVal

/-- An object's identity. -/
abbrev Ref := Nat

/-- A variable binding's identity. -/
abbrev CellRef := Nat

/-- A Private Name's identity. A class evaluation allocates one cell per
`#name` its body declares and binds it under the spelling `"#name"` in
the class's scope, so `this.#v` resolves through `Env.lookup` exactly as
`this` does. The *cell* is the name: two evaluations of one class text
allocate two cells and so declare two different private names, which is
what the specification requires and what a counter in the heap could not
give. -/
abbrev PrivateName := CellRef

/-- A symbol's identity, spelled the way a Private Name's is: the *cell*
is the name. `Symbol()` allocates a cell for the symbol it answers, so
two calls give two symbols however they are described, and the heap
needs no counter of its own to say so. The cell is immutable and empty
and is never read; it exists to be distinct. -/
abbrev SymbolId := CellRef

/-- A Symbol: an identity and an optional description. The description
rides in the value rather than in the heap so that `formatValue` and
every message that prints a key stay pure functions of the value. -/
structure Symbol where
  id : SymbolId
  description : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- SymbolDescriptiveString (20.4.3.3.1): what `String(sym)` and
`sym.toString()` answer, and what a message that names a symbol key
prints. An absent description prints as the empty one. -/
def Symbol.descriptiveString (s : Symbol) : String :=
  "Symbol(" ++ s.description.getD "" ++ ")"

/-- A JS value: a primitive from the library's tagged domain, a symbol,
or a reference into the heap's object table. Every primitive operation
the evaluator performs is the library's, so the primitive case carries
`JsVal` itself rather than a copy of it.

A symbol is the primitive the library has no tag for, and it is a
constructor here rather than a `JsVal` one because `JsVal`'s inhabitants
are values with no identity: two `Symbol("k")` calls differ, and nothing
in `Js/` can express that. It is not an object either — it has no
properties of its own, and reading one goes to `Symbol.prototype`. -/
inductive Value where
  | prim (v : JsVal)
  | obj (ref : Ref)
  | sym (s : Symbol)
deriving Repr, DecidableEq, Inhabited

/-- A property key: 6.1.7's Property Key, a String or a Symbol.

`BEq` is written out rather than derived so that `simp` unfolding a key
comparison meets a string comparison it already closes, and the `Coe`
lets every call site that spells a string key stand as it was. -/
inductive Key where
  | str (s : String)
  | sym (s : Symbol)
deriving Repr, Inhabited

/-- Key equality: strings by their text, symbols by their identity, and
`false` across the two. -/
def Key.beq : Key → Key → Bool
  | .str a, .str b => a == b
  | .sym a, .sym b => a.id == b.id
  | .str _, .sym _ => false
  | .sym _, .str _ => false

instance : BEq Key := ⟨Key.beq⟩

instance : Coe String Key := ⟨.str⟩

/-! A key comparison is the comparison of what is inside it. These four
are `@[simp]` rather than members of the evaluator's own set because they
are why retyping the property list from `String` to `Key` left every
proof where it was: without them `simp` meets an opaque `BEq Key`
instance at each of a property list's dozens of entries, and with them it
meets the `String` and `Nat` comparisons it already closes. -/

@[simp] theorem beq_key_str (a b : String) :
    (Key.str a == Key.str b) = (a == b) := rfl

@[simp] theorem beq_key_sym (a b : Symbol) :
    (Key.sym a == Key.sym b) = (a.id == b.id) := rfl

@[simp] theorem beq_key_str_sym (a : String) (b : Symbol) :
    (Key.str a == Key.sym b) = false := rfl

@[simp] theorem beq_key_sym_str (a : Symbol) (b : String) :
    (Key.sym a == Key.str b) = false := rfl

/-- A key's text, or `none` for a symbol: the question
`Object.getOwnPropertyNames`, `Object.keys`, `for`-`in`, and
`JSON.stringify` all ask, each of them being string-only by
specification. -/
def Key.str? : Key → Option String
  | .str s => some s
  | .sym _ => none

/-- SetFunctionName (10.2.9) step 1's name for a key: a string key is
itself, a symbol key with a description is that description in brackets,
and a symbol key **with none is the empty string** rather than `"[]"`. -/
def Key.functionName : Key → String
  | .str s => s
  | .sym { description := some d, .. } => "[" ++ d ++ "]"
  | .sym { description := none, .. } => ""

/-- A key's symbol, or `none` for a string. -/
def Key.sym? : Key → Option Symbol
  | .str _ => none
  | .sym s => some s

/-- How a key prints in a message: its text, or the symbol's descriptive
string. -/
instance : ToString Key where
  toString
    | .str s => s
    | .sym s => s.descriptiveString

/-- A scope chain, innermost first. Lookup takes the first match, so a
block's binding shadows an outer one of the same name without any
deletion. -/
abbrev Env := List (String × CellRef)

/-- What kind of function a closure is: whether it has a `this` of its
own, whether it may be constructed, and whether it carries a
`prototype`. An arrow pushes no `this` binding, so `this` inside one
resolves up the scope chain like any other name, which is the spec's own
mechanism; a method has a `this` but no `prototype` and no
`[[Construct]]`; a class constructor has all three and refuses to be
called without `new`. -/
inductive FuncKind where
  /-- A function declaration or expression. -/
  | ordinary
  /-- An arrow function. -/
  | arrow
  /-- A class method, getter, or setter. -/
  | method
  /-- A class constructor. `derived` is `[[ConstructorKind]]`: a derived
  constructor's `this` starts uninitialized and `super()` fills it in.
  `implicit` marks the default constructor a class without one gets,
  whose derived form forwards its arguments to the parent. -/
  | classCtor (derived : Bool) (implicit : Bool)
deriving Repr, DecidableEq, Inhabited

/-- A function's code and the scope it closed over. -/
structure Closure where
  params : List Param
  body : List Stmt
  env : Env
  kind : FuncKind
  /-- `[[HomeObject]]`: the object `super.x` reads through, which is the
  prototype for an instance method and the constructor for a static one.
  `none` for every function that is not a class element, and that is what
  makes `super` outside a method a refusal. -/
  homeObject : Option Ref := none
  /-- `[[Fields]]`: the instance fields a class constructor initializes,
  in source order. Empty for every other closure. -/
  fields : List ClassField := []
  /-- Whether a call binds an `arguments` object. ContainsArguments over
  the parameters and the body, computed once when the function object is
  made — `makeFunction` and `evalClass` are the only two that set it, and
  nothing sets it by hand. An arrow has no `arguments` of its own, so it
  is always `false` for one. Without `eval` and the `Function`
  constructor, which #376 excludes, a function that never spells the name
  cannot observe the object, so not allocating one is the specification's
  behaviour on every program this evaluator accepts. See
  `mentionsArguments` in `Tarski/Eval.lean`. -/
  needsArguments : Bool := false
deriving Repr, Inhabited

/-- The `Error` constructors the language has, in the order
`Tarski/Realm.lean` lays them out. `AggregateError` is absent by design
and not by omission: this is the set the evaluator itself throws and the
set `Project.lean`'s `errorKindOf` reads a thrown value against,
`AggregateError` is neither, and `ErrorKind.all`'s order fixes the
realm's first references and cells. It is a `NativeFn` of its own
instead. -/
inductive ErrorKind where
  | error
  | typeError
  | rangeError
  | referenceError
  | syntaxError
  | evalError
  | uriError
deriving Repr, DecidableEq, Inhabited

/-- The spelling of the kind's `name` property, which is also the
constructor's binding in the global environment. -/
def ErrorKind.name : ErrorKind → String
  | .error => "Error"
  | .typeError => "TypeError"
  | .rangeError => "RangeError"
  | .referenceError => "ReferenceError"
  | .syntaxError => "SyntaxError"
  | .evalError => "EvalError"
  | .uriError => "URIError"

/-- Every kind, in the order the realm's references are assigned. -/
def ErrorKind.all : List ErrorKind :=
  [.error, .typeError, .rangeError, .referenceError, .syntaxError, .evalError, .uriError]

/-- The `String` surface: `String`'s three statics and
`String.prototype`'s thirty-one methods, in the order `Tarski/Realm.lean`
lays them out, which is the order `StringFn.all` lists and `StringFn.ref`
counts in.

Three constructors are spelled with guillemets rather than plainly.
`«repeat»` is a Lean keyword. `«toString»` and `«toUpperCase»` are what
`scripts/check-boundary.sh` bans in method syntax under `Tarski/` — the
pattern that catches `Float.toString` and `.toUInt16` catches `.toString`
and `.toUpperCase` too — and the escape is cheaper than a constructor
whose name is not the method's.

The regex-taking members (`match`, `matchAll`, `search`), the iterator,
and Annex B's methods are not here: a `RegExp` is outside #376, the
iterator is #394's, and Annex B is not in this slice's test262
directory. -/
inductive StringFn where
  /-- `String.fromCharCode`. -/
  | fromCharCode
  /-- `String.fromCodePoint`. -/
  | fromCodePoint
  /-- `String.raw`. -/
  | raw
  /-- `String.prototype.at`. -/
  | at
  /-- `String.prototype.charAt`. -/
  | charAt
  /-- `String.prototype.charCodeAt`. -/
  | charCodeAt
  /-- `String.prototype.codePointAt`. -/
  | codePointAt
  /-- `String.prototype.concat`. -/
  | concat
  /-- `String.prototype.endsWith`. -/
  | endsWith
  /-- `String.prototype.includes`. -/
  | includes
  /-- `String.prototype.indexOf`. -/
  | indexOf
  /-- `String.prototype.isWellFormed`. -/
  | isWellFormed
  /-- `String.prototype.lastIndexOf`. -/
  | lastIndexOf
  /-- `String.prototype.localeCompare`. -/
  | localeCompare
  /-- `String.prototype.normalize`. -/
  | normalize
  /-- `String.prototype.padEnd`. -/
  | padEnd
  /-- `String.prototype.padStart`. -/
  | padStart
  /-- `String.prototype.repeat`. -/
  | «repeat»
  /-- `String.prototype.replace`. -/
  | replace
  /-- `String.prototype.replaceAll`. -/
  | replaceAll
  /-- `String.prototype.slice`. -/
  | slice
  /-- `String.prototype.split`. -/
  | split
  /-- `String.prototype.startsWith`. -/
  | startsWith
  /-- `String.prototype.substring`. -/
  | substring
  /-- `String.prototype.toLocaleLowerCase`. -/
  | toLocaleLowerCase
  /-- `String.prototype.toLocaleUpperCase`. -/
  | toLocaleUpperCase
  /-- `String.prototype.toLowerCase`. -/
  | toLowerCase
  /-- `String.prototype.toString`. -/
  | «toString»
  /-- `String.prototype.toUpperCase`. -/
  | «toUpperCase»
  /-- `String.prototype.toWellFormed`. -/
  | toWellFormed
  /-- `String.prototype.trim`. -/
  | trim
  /-- `String.prototype.trimEnd`. -/
  | trimEnd
  /-- `String.prototype.trimStart`. -/
  | trimStart
  /-- `String.prototype.valueOf`. -/
  | valueOf
deriving Repr, DecidableEq, Inhabited

/-- Every member, in the realm's order: the three statics and then the
thirty-one prototype methods, which is the order `String.prototype`'s
property list is in and the order `StringFn.ref` counts references in. -/
def StringFn.all : List StringFn :=
  [ .fromCharCode, .fromCodePoint, .raw,
    .at, .charAt, .charCodeAt, .codePointAt, .concat, .endsWith, .includes, .indexOf,
    .isWellFormed, .lastIndexOf, .localeCompare, .normalize, .padEnd, .padStart,
    .«repeat», .replace, .replaceAll, .slice, .split, .startsWith, .substring,
    .toLocaleLowerCase, .toLocaleUpperCase, .toLowerCase, .«toString», .«toUpperCase»,
    .toWellFormed, .trim, .trimEnd, .trimStart, .valueOf ]

/-- A built-in function's body: an identity Lean dispatches on, not a
`Closure`. A built-in is not self-hosted for two reasons — a native
constructor must be able to construct when called without `new`, which
no AST spells, and `[[ErrorData]]`-style internal behaviour has no source
form at all. Later slices add constructors here and an arm to
`callNative` for each.

**Every name here is prefixed by the intrinsic it belongs to** —
`mathAbs`, not `abs`; `numberIsNaN`, not `isNaN` — and not only for
readability: `scripts/check-boundary.sh` matches method-syntax `Float`
operations by name, so a constructor called `.abs`, `.floor`, `.sqrt`,
`.round`, `.ceil`, `.pow`, `.exp`, `.isNaN`, or `.isFinite` would trip
the arithmetic boundary wherever it was projected. -/
inductive NativeFn where
  /-- One of the `Error` constructors. -/
  | errorCtor (kind : ErrorKind)
  /-- `Error.prototype.toString`. -/
  | errorToString
  /-- `String`: ToString of its argument when it is called, and the
  wrapper object when it is `new`ed. `constructNative` is what `new`
  does. -/
  | stringCtor
  /-- One of `String`'s statics or one of `String.prototype`'s methods.
  The surface is **one** `NativeFn` constructor over a sub-enum rather
  than thirty-four constructors of its own, because `NativeFn` is already
  at the ceiling `Tarski/Simp.lean` documents: a `match` over sixty
  constructors with a body that size has no equation lemmas, which is why
  `callReflectNative` was split out of `callNative`, and thirty-four more
  arms would put the dispatch past it again. -/
  | string (f : StringFn)
  /-- `Object`, the constructor. -/
  | objectCtor
  /-- `Object.is`. -/
  | objectIs
  /-- `Object.keys`. -/
  | objectKeys
  /-- `Object.prototype.hasOwnProperty`. -/
  | objectHasOwnProperty
  /-- `Array`, the constructor. -/
  | arrayCtor
  /-- `Array.isArray`. -/
  | arrayIsArray
  /-- `Array.prototype.push`. -/
  | arrayPush
  /-- `Array.prototype.join`. -/
  | arrayJoin
  /-- `print`, the test262 host's one output binding. `EvalM` has no IO,
  so ToString of the first argument is appended to the intrinsic array
  `%PrintLog%` and the binary writes the log out after the run. -/
  | print
  /-- `console.log`, the second host output binding and the one
  `lakatos exe` forwards to stdout. `print`'s twin: ToString of **every**
  argument, joined by one space, appended as one line to `%PrintLog%`, so
  a run's output is a single sequence in program order however it was
  written. Two differences from Node, both named in the README as limits
  of `exe`: Node inspects an object where this takes its ToString, and
  Node prints `-0` where ToString gives `0`. -/
  | consoleLog
  /-- `Number`, as a converter and as a wrapper constructor. -/
  | numberCtor
  /-- `Number.isFinite`. -/
  | numberIsFinite
  /-- `Number.isInteger`. -/
  | numberIsInteger
  /-- `Number.isNaN`. -/
  | numberIsNaN
  /-- `Number.isSafeInteger`. -/
  | numberIsSafeInteger
  /-- `Number.prototype.toString`. -/
  | numberToString
  /-- `Number.prototype.valueOf`. -/
  | numberValueOf
  /-- `Number.prototype.toFixed`. -/
  | numberToFixed
  /-- `Number.prototype.toExponential`. -/
  | numberToExponential
  /-- `Number.prototype.toPrecision`. -/
  | numberToPrecision
  /-- `Number.prototype.toLocaleString`, which is `toString()` here:
  there is no locale, ECMA-402 being outside this epic, and the method
  exists so that the tests that read its descriptor fail on the
  descriptor rather than on its absence. -/
  | numberToLocaleString
  /-- The global `parseFloat`, which is also `Number.parseFloat` — one
  function object bound in two places, as the specification has it. -/
  | parseFloat
  /-- The global `parseInt`, which is also `Number.parseInt`. -/
  | parseInt
  /-- `Boolean`, as a converter and as a wrapper constructor. -/
  | booleanCtor
  /-- `Boolean.prototype.toString`. -/
  | booleanToString
  /-- `Boolean.prototype.valueOf`. -/
  | booleanValueOf
  /-- `Math.abs`. -/
  | mathAbs
  /-- `Math.ceil`. -/
  | mathCeil
  /-- `Math.floor`. -/
  | mathFloor
  /-- `Math.fround`. -/
  | mathFround
  /-- `Math.round`. -/
  | mathRound
  /-- `Math.sign`. -/
  | mathSign
  /-- `Math.sqrt`. -/
  | mathSqrt
  /-- `Math.trunc`. -/
  | mathTrunc
  /-- `Math.max`, variadic over the library's binary `tsMax`. -/
  | mathMax
  /-- `Math.min`, variadic over the library's binary `tsMin`. -/
  | mathMin
  /-- `Math.pow`, the library's `tsPow` — the same definition `**` is. -/
  | mathPow
  /-- `%ThrowTypeError%` (10.2.4.1): the one function per realm that does
  nothing but throw a `TypeError`. It is both halves of a strict
  `arguments` object's `callee` accessor, which is why it must be a
  single object rather than a closure made per call. It has no
  `[[Construct]]`. -/
  | throwTypeError
  /-- `Object.prototype.toString`. -/
  | objectProtoToString
  /-- `Object.prototype.valueOf`. -/
  | objectProtoValueOf
  /-- `Object.prototype.toLocaleString`, which Invokes `this.toString()`
  as 20.1.3.5 has it. -/
  | objectProtoToLocaleString
  /-- `Object.prototype.isPrototypeOf`. -/
  | objectProtoIsPrototypeOf
  /-- `Object.prototype.propertyIsEnumerable`. -/
  | objectProtoPropertyIsEnumerable
  /-- `Object.assign`. -/
  | objectAssign
  /-- `Object.create`. -/
  | objectCreate
  /-- `Object.defineProperties`. -/
  | objectDefineProperties
  /-- `Object.defineProperty`. -/
  | objectDefineProperty
  /-- `Object.entries`. -/
  | objectEntries
  /-- `Object.freeze`. -/
  | objectFreeze
  /-- `Object.getOwnPropertyDescriptor`. -/
  | objectGetOwnPropertyDescriptor
  /-- `Object.getOwnPropertyDescriptors`. -/
  | objectGetOwnPropertyDescriptors
  /-- `Object.getOwnPropertyNames`. -/
  | objectGetOwnPropertyNames
  /-- `Object.getPrototypeOf`. -/
  | objectGetPrototypeOf
  /-- `Object.hasOwn`. -/
  | objectHasOwn
  /-- `Object.isExtensible`. -/
  | objectIsExtensible
  /-- `Object.isFrozen`. -/
  | objectIsFrozen
  /-- `Object.isSealed`. -/
  | objectIsSealed
  /-- `Object.preventExtensions`. -/
  | objectPreventExtensions
  /-- `Object.seal`. -/
  | objectSeal
  /-- `Object.setPrototypeOf`. -/
  | objectSetPrototypeOf
  /-- `Object.values`. -/
  | objectValues
  /-- `%Function.prototype%` itself, which is callable and answers
  `undefined` whatever it is given (20.2.3). -/
  | functionProto
  /-- The `Function` constructor. The *object* exists, because every
  `call`/`apply`/`bind` spelling and every test that reads a function's
  prototype chain goes through it; calling it is out of the epic's scope
  (`eval` by another name), so the decoder refuses `Function(...)` by
  name and an alias meets this arm's `TypeError`. -/
  | functionCtor
  /-- `Function.prototype.call`. -/
  | functionCall
  /-- `Function.prototype.apply`. -/
  | functionApply
  /-- `Function.prototype.bind`. -/
  | functionBind
  /-- `Function.prototype.toString`. -/
  | functionToString
  /-- `Symbol`, the constructor. It has a `[[Construct]]` that throws:
  `isConstructor(Symbol)` is true and `class X extends Symbol` is
  well-formed, while `new Symbol()` is a `TypeError` (20.4.1). -/
  | symbolCtor
  /-- `Symbol.for`. -/
  | symbolFor
  /-- `Symbol.keyFor`. -/
  | symbolKeyFor
  /-- `Symbol.prototype.toString`. -/
  | symbolProtoToString
  /-- `Symbol.prototype.valueOf`. -/
  | symbolProtoValueOf
  /-- `get Symbol.prototype.description`. -/
  | symbolDescription
  /-- `Symbol.prototype[@@toPrimitive]`. -/
  | symbolToPrimitive
  /-- `JSON.parse`. -/
  | jsonParse
  /-- `JSON.stringify`. -/
  | jsonStringify
  /-- The `AggregateError` constructor. -/
  | aggregateErrorCtor
  /-- `Function.prototype[@@hasInstance]`. -/
  | functionHasInstance
  /-- `Object.getOwnPropertySymbols`. -/
  | objectGetOwnPropertySymbols
  /-- `Error.isError`. -/
  | errorIsError
deriving Repr, DecidableEq, Inhabited

/-- A bound function exotic object's three internal slots plus the one
fact about its target a walk would otherwise have to recompute.
BoundFunctionCreate (10.4.1.3) decides `[[Construct]]`'s presence once,
from a target whose constructibility never changes, so it is data here
rather than a read of the heap. -/
structure BoundFunction where
  /-- `[[BoundTargetFunction]]`. -/
  target : Ref
  /-- `[[BoundThis]]`. -/
  boundThis : Value
  /-- `[[BoundArguments]]`, prepended to every call's arguments. -/
  boundArgs : List Value
  /-- Whether the target had a `[[Construct]]` when `bind` ran. -/
  constructs : Bool
deriving Repr, Inhabited

/-- `[[Call]]`: user code, a built-in, or a bound function. -/
inductive Callable where
  | closure (c : Closure)
  | native (f : NativeFn)
  /-- A bound function exotic object (10.4.1): calling it calls the
  target with the bound `this` and the bound arguments in front. -/
  | bound (b : BoundFunction)
deriving Repr, Inhabited

/-- How exotic an object is. `ordinary` is every object with no
internal behaviour of its own; `array` is the Array exotic object, and
its `length` lives here rather than among the properties for three
reasons: it is then never enumerated by `Object.keys`, never shadowed by
an ordinary write, and truncation is one field write rather than a scan
plus a property update. **`length`'s one variable attribute lives beside
its value** for that same reason: `[[Writable]]` is the only attribute a
`length` can change, `Object.defineProperty(xs, "length", …)` is the only
thing that changes it, and a second place for one property's state would
be a place to forget. `number` and `boolean` are the Number and Boolean
wrapper objects, carrying `[[NumberData]]` and `[[BooleanData]]` the same
way — a field, not a property, so `Object.keys(new Number(1))` is empty
and no write can forge one. `error` is `[[ErrorData]]`, which has no
other home and which `Object.prototype.toString` reads as `Error`;
`arguments` is the unmapped arguments object, ordinary in every respect
but the `[[ParameterMap]]` slot, which is what that same `toString`
reads to answer `[object Arguments]`, so the kind *is* that slot.
`hasOwn`, `ownKeys`, and `truncate` treat `arguments` as ordinary. A kind
with a `Float` in it still derives `DecidableEq`, because propositional
equality on `Float` is SameValue (`Js/Val.lean` says so), which is the
right test for a `[[NumberData]]`. `symbol` is the Symbol wrapper object
`Object(sym)` builds, carrying `[[SymbolData]]`. `string` is
`[[StringData]]`, and it is the **opposite** arrangement from the array's:
a String exotic object's index properties are synthesized from the slot,
because they are unbounded data an object should not copy, while its
`length` is a real own `constant` property, because StringCreate
(10.4.3.4) defines it once with DefinePropertyOrThrow and it can never
change — which is also what puts it first among the non-index keys. -/
inductive ObjKind where
  | ordinary
  | array (length : Nat) (lengthWritable : Bool)
  | number (value : Float)
  | boolean (value : Bool)
  | string (value : JsString)
  | arguments
  | error
  | symbol (value : Symbol)
deriving Repr, DecidableEq, Inhabited

/-- An accessor property's two functions. Named `getter` and `setter`
rather than `get` and `set` because those two spellings are the state
monad's, and a field projection of either name would shadow one wherever
an `Obj` was open. Both are `Option`: a property may have only a getter,
only a setter, or — after a `get x` and a `set x` on one name — both. -/
structure Accessor where
  /-- `[[Get]]`. A read of a getter-less accessor property is
  `undefined`. -/
  getter : Option Value := none
  /-- `[[Set]]`. A write to a setter-less accessor property is a
  `TypeError` in strict mode. -/
  setter : Option Value := none
deriving Repr, DecidableEq, Inhabited

/-- A property's value half: 6.1.7.1's two descriptor kinds. A property
is one or the other and never both, which is why this is a sum rather
than four optional fields. -/
inductive PropSlot where
  /-- A data property: `[[Value]]` and `[[Writable]]`. -/
  | data (value : Value) (writable : Bool)
  /-- An accessor property: `[[Get]]` and `[[Set]]`. -/
  | accessor (a : Accessor)
deriving Repr, DecidableEq, Inhabited

/-- An own property: 6.1.7.1's attribute table, with the two attributes
every property has beside the ones its kind has. -/
structure Property where
  /-- The value half, and which kind of property this is. -/
  slot : PropSlot
  /-- `[[Enumerable]]`: whether `for`-`in` and `Object.keys` see it. -/
  enumerable : Bool
  /-- `[[Configurable]]`: whether it may be deleted or redefined. -/
  configurable : Bool
deriving Repr, DecidableEq, Inhabited

/-- A data property with every attribute set: CreateDataProperty's
result, and so what an object literal's member, an array's element, a
public class field, and an ordinary write all build. -/
@[reducible] def Property.ordinary (v : Value) : Property :=
  { slot := .data v true, enumerable := true, configurable := true }

/-- Writable and configurable but not enumerable: the attributes every
built-in method has, and the ones `constructor` on a prototype, `name`
and `message` on an `Error.prototype`, a class method, and the `message`
an `Error` constructor sets all carry. -/
@[reducible] def Property.method (v : Value) : Property :=
  { slot := .data v true, enumerable := false, configurable := true }

/-- Configurable and nothing else: a function's `length` and `name`, so
that `f.name = "x"` refuses in strict mode while
`Object.defineProperty(f, "name", …)` succeeds — which is exactly what
test262's `propertyHelper.js` verifies on every built-in. -/
@[reducible] def Property.attribute (v : Value) : Property :=
  { slot := .data v false, enumerable := false, configurable := true }

/-- No attribute at all: `Number.EPSILON`, `Math.PI`, a constructor's
`prototype`. -/
@[reducible] def Property.constant (v : Value) : Property :=
  { slot := .data v false, enumerable := false, configurable := false }

/-- Writable and nothing else: an ordinary function's own `prototype`
property (10.2.5 MakeConstructor), which a script may replace but not
delete or make enumerable. -/
@[reducible] def Property.functionPrototype (v : Value) : Property :=
  { slot := .data v true, enumerable := false, configurable := false }

/-- A data property's value; `none` for an accessor. -/
def Property.value? : Property → Option Value
  | { slot := .data v _, .. } => some v
  | { slot := .accessor _, .. } => none

/-- A data property's `[[Writable]]`; `none` for an accessor. -/
def Property.writable? : Property → Option Bool
  | { slot := .data _ w, .. } => some w
  | { slot := .accessor _, .. } => none

/-- An accessor property's two halves; `none` for a data property. -/
def Property.accessor? : Property → Option Accessor
  | { slot := .accessor a, .. } => some a
  | { slot := .data _ _, .. } => none

/-- Whether the property is an accessor property. -/
def Property.isAccessor (p : Property) : Bool :=
  match p.slot with
  | .accessor _ => true
  | .data _ _ => false

/-- An ordinary object: a prototype link, its own properties in
insertion order, whether it may grow, and — for a function — what
calling it does. -/
structure Obj where
  /-- `[[Prototype]]`. `none` is the null prototype. -/
  proto : Option Ref := none
  /-- Own properties, in insertion order, **data and accessor together**:
  a key names at most one property, which is what makes redefining a
  getter as a data property the specification's replacement rather than
  two properties of one name, and what lets `ownKeys` interleave the two
  kinds as OrdinaryOwnPropertyKeys requires. An array's elements are
  here, under their index keys; its `length` is not. -/
  properties : List (Key × Property) := []
  /-- `[[Call]]`. An object with one is a function. -/
  callable : Option Callable := none
  /-- The exotic-object classification. Defaulted, so an ordinary
  object's literal says nothing about it. -/
  kind : ObjKind := .ordinary
  /-- `[[Extensible]]`. A field rather than a property because
  `Object.preventExtensions` changes a *state*: no key names it, and
  nothing a script writes can forge one. -/
  extensible : Bool := true
  /-- `[[PrivateElements]]`, restricted to fields — a private method or
  accessor is a decoder refusal, so no other kind can arrive. These are
  not properties: no key names them, `Object.keys` cannot see them, and
  a prototype walk never reaches them. -/
  privates : List (PrivateName × Value) := []
deriving Repr, Inhabited

/-- A variable binding. `mutable` is `false` for `const`, which is what
makes assignment to a `const` a runtime refusal rather than a silent
write. `value` is `none` between the cell's allocation and its
initializer — the temporal dead zone. -/
structure Cell where
  mutable : Bool
  value : Option Value := none
deriving Repr, Inhabited

/-- The mutable state of a run: variable bindings and objects. -/
structure Heap where
  cells : Array Cell := #[]
  objects : Array Obj := #[]
deriving Repr, Inhabited

/-- An abrupt completion — the evaluator's error channel. Each of the
three jumps carries the completion record's `[[Value]]`: a `break` or a
`continue` carries the running completion value of the statement lists it
is crossing, which is what UpdateEmpty fills in the spec and what
`evalStmt`'s threaded accumulator computes here, so
`while (true) { 2; break; }` completes with `2`. A `label` of `none` is
the unlabelled form. -/
inductive Completion where
  | throw (value : Value)
  | «return» (value : Value)
  | «break» (label : Option String) (value : Option Value)
  | «continue» (label : Option String) (value : Option Value)
deriving Repr, DecidableEq, Inhabited

/-- The heap with no realm in it: no intrinsics, no global bindings.
`Tarski/Realm.lean`'s `Heap.initial` is what a script actually starts
from; this is what that one is built on top of, and what a proof about
the object operations alone uses. -/
def Heap.empty : Heap := {}

/-- Allocate a binding, answering its reference and the grown heap. -/
def Heap.alloc (h : Heap) (c : Cell) : CellRef × Heap :=
  (h.cells.size, { h with cells := h.cells.push c })

/-- Read a binding. `none` is impossible for a reference the evaluator
handed out: every `CellRef` in an `Env` indexes a cell that was allocated
before it was named. -/
def Heap.read (h : Heap) (r : CellRef) : Option Cell :=
  h.cells[r]?

/-- Write a binding's value, leaving its mutability alone. Out-of-range
references leave the heap unchanged, by the same impossibility. -/
def Heap.write (h : Heap) (r : CellRef) (v : Value) : Heap :=
  match h.cells[r]? with
  | some c => { h with cells := h.cells.set! r { c with value := some v } }
  | none => h

/-- Allocate an object, answering its reference and the grown heap. -/
def Heap.allocObj (h : Heap) (o : Obj) : Ref × Heap :=
  (h.objects.size, { h with objects := h.objects.push o })

/-- Read an object. -/
def Heap.readObj (h : Heap) (r : Ref) : Option Obj :=
  h.objects[r]?

/-- Replace an object. Out-of-range references leave the heap unchanged,
as `Heap.write` does. -/
def Heap.writeObj (h : Heap) (r : Ref) (o : Obj) : Heap :=
  match h.objects[r]? with
  | some _ => { h with objects := h.objects.set! r o }
  | none => h

/-- `Object.is` on values: the library's `sameValue` on primitives —
which is what makes `Object.is(NaN, NaN)` true and `Object.is(0, -0)`
false — reference identity on objects, and `false` across the two. It
lives here rather than in `Eval` because `Obj.applyDescriptor` is a pure
function and 10.1.6.3 asks the question twice. -/
def sameValueValue : Value → Value → Bool
  | .prim a, .prim b => JsVal.sameValue a b
  | .obj r₁, .obj r₂ => r₁ == r₂
  | .sym a, .sym b => a.id == b.id
  | .prim _, .obj _ => false
  | .prim _, .sym _ => false
  | .obj _, .prim _ => false
  | .obj _, .sym _ => false
  | .sym _, .prim _ => false
  | .sym _, .obj _ => false

/-- Find a key in a property list. -/
def propGet : List (Key × Property) → Key → Option Property
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else propGet rest key

/-- Create or overwrite a key in a property list. An existing key keeps
its place in the insertion order; a new one goes last. -/
def propSet : List (Key × Property) → Key → Property → List (Key × Property)
  | [], key, v => [(key, v)]
  | (k, w) :: rest, key, v =>
    if k == key then (key, v) :: rest else (k, w) :: propSet rest key v

/-- Drop a key from a property list, keeping the rest in order. -/
def propDrop : List (Key × Property) → Key → List (Key × Property)
  | [], _ => []
  | (k, v) :: rest, key => if k == key then rest else (k, v) :: propDrop rest key

/-- An own property, attributes and all, or `none` if the object does
not have one under that key. An array's `length` is not here: it lives in
the kind, and `Eval.findProperty` synthesizes its descriptor. -/
def Obj.getOwnProperty (o : Obj) (key : Key) : Option Property :=
  propGet o.properties key

/-- An own *data* property's value, or `none` if the object has no own
property under that key or has an accessor there. Walking the prototype
chain is `Eval`'s business: it runs user code, so it cannot be a pure
function of the heap. -/
def Obj.getOwn (o : Obj) (key : Key) : Option Value :=
  match o.getOwnProperty key with
  | some p => p.value?
  | none => none

/-- An own accessor property, or `none` if the object has no own
property under that key or has a data property there. -/
def Obj.getOwnAccessor (o : Obj) (key : Key) : Option Accessor :=
  match o.getOwnProperty key with
  | some p => p.accessor?
  | none => none

/-- Define an own property with the attributes given. A *definition*,
not a write: an accessor of the same name is replaced rather than
called, which is what makes a class field ignore a prototype setter. An
existing key keeps its place in the insertion order. -/
def Obj.define (o : Obj) (key : Key) (p : Property) : Obj :=
  { o with properties := propSet o.properties key p }

/-- Define one half of an accessor property, merging into an accessor
already under that key so that a `get x` and a `set x` make one property
with two halves, and replacing a data property outright. An absent half
leaves whatever is there standing, which is
ValidateAndApplyPropertyDescriptor's own rule: a descriptor without a
`[[Set]]` field does not erase one. -/
def Obj.defineAccessorHalf (o : Obj) (key : Key) (getter setter : Option Value)
    (enumerable configurable : Bool) : Obj :=
  let a : Accessor :=
    match o.getOwnAccessor key with
    | some old =>
      { getter := match getter with | some _ => getter | none => old.getter,
        setter := match setter with | some _ => setter | none => old.setter }
    | none => { getter, setter }
  o.define key { slot := .accessor a, enumerable, configurable }

/-- OrdinarySet's write half: an existing *data* property keeps its
attributes and takes the value, and a key that is not there becomes an
ordinary data property. The writability and extensibility checks are
`Eval.setProp`'s, which has the `TypeError`s to throw. -/
def Obj.setOwn (o : Obj) (key : Key) (v : Value) : Obj :=
  match o.getOwnProperty key with
  | some p => o.define key { p with slot := .data v (p.writable?.getD true) }
  | none => o.define key (Property.ordinary v)

/-- `[[Delete]]`'s write half: drop the key. The configurability check is
`Eval.deleteProp`'s. -/
def Obj.remove (o : Obj) (key : Key) : Obj :=
  { o with properties := propDrop o.properties key }

/-- Find a private element. -/
def privateGet : List (PrivateName × Value) → PrivateName → Option Value
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else privateGet rest key

/-- Overwrite a private element that is already there. -/
def privateSet : List (PrivateName × Value) → PrivateName → Value → List (PrivateName × Value)
  | [], _, _ => []
  | (k, w) :: rest, key, v =>
    if k == key then (key, v) :: rest else (k, w) :: privateSet rest key v

/-- A private element's value, or `none` when the object's class did not
declare it — which is the whole of a private read's type check. -/
def Obj.getPrivate (o : Obj) (k : PrivateName) : Option Value :=
  privateGet o.privates k

/-- Write a private element that is already there. A private field is
never created by a write: only field initialization adds one. -/
def Obj.setPrivate (o : Obj) (k : PrivateName) (v : Value) : Obj :=
  { o with privates := privateSet o.privates k v }

/-- PrivateFieldAdd's half that cannot fail: append the element. The
already-present check is `Eval`'s, which has the `TypeError` to throw. -/
def Obj.addPrivate (o : Obj) (k : PrivateName) (v : Value) : Obj :=
  { o with privates := o.privates ++ [(k, v)] }

/-- Resolve a name in a scope chain: the innermost binding wins. -/
def Env.lookup : Env → String → Option CellRef
  | [], _ => none
  | (n, r) :: rest, name => if n == name then some r else Env.lookup rest name

/-- A `Nat` as a Number. This is the one widening the evaluator performs
itself — a length or an index becoming a JS value — and it is exact:
`Nat.toFloat` is `Float.ofNat`, a definition with no `extern`, so the
kernel reduces it, and every length this slice can build is far below
2^53. `scripts/check-boundary.sh`'s header names this spelling; the
conversions in the other direction go through `uint32Of?`. -/
def Value.ofNat (n : Nat) : Value := .prim (.num n.toFloat)

/-- Fold a run of decimal digits onto an accumulator, refusing anything
that is not one. Core's `String.toNat?` accepts digit separators
(`"1_0".toNat? = some 10`), which is not what an array index is, so the
parse is written out here. -/
def digitsToNat : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: rest, acc =>
    if c.isDigit then digitsToNat rest (acc * 10 + (c.toNat - '0'.toNat)) else none

/-- A property key read as an array index: CanonicalNumericIndexString
restricted to the indices an array may hold. Non-empty, digits only, no
leading zero unless the string is `"0"`, and below 2^32 - 1, so that
`xs["01"]` and `xs["1.0"]` are ordinary string keys that do not grow a
`length`. -/
def arrayIndex? (key : String) : Option Nat :=
  match key.toList with
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | cs =>
    match digitsToNat cs 0 with
    | some n => if n < 4294967295 then some n else none
    | none => none

/-- A *key* read as an array index: a symbol is never one. -/
def Key.arrayIndex? : Key → Option Nat
  | .str s => _root_.Tarski.arrayIndex? s
  | .sym _ => none

/-- Whether an object is an Array exotic object. -/
def Obj.isArray (o : Obj) : Bool :=
  match o.kind with
  | .array _ _ => true
  | _ => false

/-- Whether an object is a String exotic object. -/
def Obj.isString (o : Obj) : Bool :=
  match o.kind with
  | .string _ => true
  | _ => false

/-- `[[StringData]]`, or `none` for anything that is not a String
exotic object. -/
def Obj.stringData? (o : Obj) : Option JsString :=
  match o.kind with
  | .string s => some s
  | _ => none

/-- A String exotic object's own index property (10.4.3.5): the one-unit
string at the index, enumerable, neither writable nor configurable. The
`none` arm is unreachable — every caller has already checked the index
against the length — and answers `undefined` rather than inventing a
`get!`. -/
def Obj.stringIndexProperty (s : JsString) (i : Nat) : Property :=
  { slot := .data (.prim (.str ((s.unitAt? i).getD (JsString.ofString "")))) false,
    enumerable := true, configurable := false }

/-- An array's live `length` and its `[[Writable]]`, or `none` for
anything that is not an Array exotic object. -/
def Obj.arrayLength? (o : Obj) : Option (Nat × Bool) :=
  match o.kind with
  | .array n w => some (n, w)
  | _ => none

/-- `[[GetOwnProperty]]` (10.1.5.1, plus 10.4.2.1 and 10.4.3.5 for the
two exotic cases): the own property under a key, **with an array's
`length` and a String object's indices synthesized** — each an own
property that does not live in the property list. A String object's
`length` is not synthesized: it is a real `constant` property, because
StringCreate defines it once and it can never change.

This is the one `[[GetOwnProperty]]`: `getFrom`, `findProperty`,
`deleteProp`, and `applyDescriptor` all read it, so the array's `length`
and the string's indices are answered in one place. -/
def Obj.ownProperty (o : Obj) (key : Key) : Option Property :=
  match o.kind with
  | .array n w =>
    if key == Key.str "length" then
      some { slot := .data (Value.ofNat n) w, enumerable := false, configurable := false }
    else o.getOwnProperty key
  | .string s =>
    match key.arrayIndex? with
    | some i => if i < s.length then some (Obj.stringIndexProperty s i) else o.getOwnProperty key
    | none => o.getOwnProperty key
  | _ => o.getOwnProperty key

/-- `[[GetOwnProperty]]` reduced to a yes or no, which is all
`Object.prototype.hasOwnProperty` and `Object.hasOwn` ask. -/
def Obj.hasOwn (o : Obj) (key : Key) : Bool :=
  (o.ownProperty key).isSome

/-- SetIntegrityLevel (7.3.15) as a pure function: the object stops being
extensible and every own property stops being configurable, and under
`frozen` every own *data* property stops being writable too — an array's
`length` among them, which is why the kind's bit is set here. -/
def Obj.setIntegrity (o : Obj) (frozen : Bool) : Obj :=
  { o with
    extensible := false,
    kind := match o.kind with
      | .array n w => .array n (if frozen then false else w)
      | k => k,
    properties := o.properties.map (fun p =>
      (p.1,
        { p.2 with
          configurable := false,
          slot := match p.2.slot with
            | .data v w => .data v (if frozen then false else w)
            | a => a })) }

/-- TestIntegrityLevel (7.3.16), the question `Object.isFrozen` and
`Object.isSealed` ask. -/
def Obj.testIntegrity (o : Obj) (frozen : Bool) : Bool :=
  !o.extensible
    && (match o.kind with
        | .array _ w => !(frozen && w)
        | _ => true)
    && o.properties.all (fun p =>
        !p.2.configurable
          && (!frozen ||
              match p.2.slot with
              | .data _ w => !w
              | .accessor _ => true))

/-- `Obj.truncate`'s loop: the doomed index keys from the top down, each
dropped while it is configurable. The first non-configurable one stops
the scan and fixes the length at one past it, which is 10.4.2.4 steps
12–14 exactly. -/
def truncateDrop (props : List (Key × Property)) (reached : Nat) :
    List (Nat × Key) → List (Key × Property) × Nat
  | [] => (props, reached)
  | (i, k) :: rest =>
    match propGet props k with
    | some p =>
      if p.configurable then truncateDrop (propDrop props k) reached rest
      else (props, i + 1)
    | none => truncateDrop props reached rest

/-- ArraySetLength's shortening half (10.4.2.4 steps 12–14): drop every
element at an index at or past the new length, **from the top down and
stopping at the first non-configurable one**, and answer the length the
scan actually reached. Growing is the same operation with nothing to
drop. `length`'s own `[[Writable]]` is not touched here: the caller
decides whether the write was allowed at all. -/
def Obj.truncate (o : Obj) (n : Nat) : Obj × Nat :=
  let w := match o.kind with
    | .array _ lw => lw
    | _ => true
  let doomed :=
    (o.properties.filterMap (fun p =>
      match Key.arrayIndex? p.1 with
      | some i => if n ≤ i then some (i, p.1) else none
      | none => none)).mergeSort (fun a b => decide (b.1 ≤ a.1))
  let (props, reached) := truncateDrop o.properties n doomed
  ({ o with kind := .array reached w, properties := props }, reached)

/-- OrdinaryOwnPropertyKeys (10.1.11.1) in full: the index keys in
ascending numeric order, then every other string key in insertion order,
then **the symbol keys in insertion order** — data and accessor
properties interleaved, because they are one list. An array's `length`
joins after the index keys and before the rest: it is an own property,
so `Object.getOwnPropertyNames([1])` is `["0", "length"]`, even though it
does not live in the property list. A String object's index keys come
first for the same reason and can never collide with the property list's,
an index below the length being unwritable. -/
def Obj.ownKeys (o : Obj) : List Key :=
  let keys := o.properties.map (·.1)
  let synthesized : List Key := match o.kind with
    | .string s => (List.range s.length).map (fun i => Key.str (Nat.repr i))
    | _ => []
  let indexed := keys.filterMap (fun k => k.arrayIndex?.map (fun i => (i, k)))
  synthesized ++ (indexed.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    ++ (if o.isArray then [Key.str "length"] else [])
    ++ keys.filter (fun k => k.arrayIndex?.isNone && k.str?.isSome)
    ++ keys.filter (fun k => k.sym?.isSome)

/-- The own *string* keys, in `ownKeys` order: what
`Object.getOwnPropertyNames` answers. -/
def Obj.stringKeys (o : Obj) : List String :=
  o.ownKeys.filterMap Key.str?

/-- The own *symbol* keys, in `ownKeys` order: what
`Object.getOwnPropertySymbols` answers. -/
def Obj.symbolKeys (o : Obj) : List Symbol :=
  o.ownKeys.filterMap Key.sym?

/-- The own keys `Object.keys` and `for`-`in` see: the string keys
filtered by `[[Enumerable]]` — through `ownProperty`, so a String
object's synthesized indices are seen. EnumerableOwnProperties and
EnumerateObjectProperties are string-only by specification, so a
symbol-keyed property is never here however enumerable it is. An array's
`length` is non-enumerable, so it never appears either. -/
def Obj.enumerableKeys (o : Obj) : List String :=
  o.stringKeys.filter (fun k =>
    match o.ownProperty (.str k) with
    | some p => p.enumerable
    | none => false)

/-- A list of values as index-keyed ordinary data properties, numbered
from `start`. -/
def indexProps (start : Nat) : List Value → List (Key × Property)
  | [] => []
  | v :: rest => (.str (Nat.repr start), Property.ordinary v) :: indexProps (start + 1) rest

/-- ArrayCreate's object: the elements under their index keys, the
length — writable, as ArrayCreate leaves it — in the kind, and the given
prototype. -/
def Obj.array (proto : Option Ref) (elements : List Value) : Obj :=
  { kind := .array elements.length true, proto, properties := indexProps 0 elements }

/-- StringCreate (10.4.3.4): the String exotic object around a string.
Its `length` is a real own property — non-writable, non-enumerable,
non-configurable — defined once, which is what puts it after the indices
and before everything else in `ownKeys`; the indices themselves are
synthesized from the slot. `@[reducible]`, so `String.prototype` keeps
`Heap.initial` a literal to `simp`. -/
@[reducible] def Obj.stringWrapper (proto : Option Ref) (s : JsString) : Obj :=
  { proto, kind := .string s,
    properties := [("length", Property.constant (Value.ofNat s.length))] }

/-- A *partial* Property Descriptor (6.2.6): every field may be absent,
and absence is not the same as `undefined`. `{ get: undefined }` is an
accessor descriptor whose `[[Get]]` is `undefined`, while `{}` has no
`[[Get]]` at all, so an absent field is `none` and a present one is
`some` of whatever was there. -/
structure Descriptor where
  /-- `[[Value]]`. -/
  value : Option Value := none
  /-- `[[Get]]`. -/
  getter : Option Value := none
  /-- `[[Set]]`. -/
  setter : Option Value := none
  /-- `[[Writable]]`. -/
  writable : Option Bool := none
  /-- `[[Enumerable]]`. -/
  enumerable : Option Bool := none
  /-- `[[Configurable]]`. -/
  configurable : Option Bool := none
deriving Repr, DecidableEq, Inhabited

/-- A descriptor's accessor half as an `Accessor` stores it: a `[[Get]]`
or `[[Set]]` of `undefined` is stored as **absent**, because the two are
the same property — a read of either answers `undefined` rather than
calling one, and a write to either refuses. The *descriptor* still
distinguishes them, which is what makes `{ get: undefined }` an accessor
descriptor and `{}` a generic one. -/
def accessorHalf : Option Value → Option Value
  | some (.prim .undef) => none
  | h => h

/-- IsAccessorDescriptor (6.2.6.1). -/
def Descriptor.isAccessor (d : Descriptor) : Bool :=
  d.getter.isSome || d.setter.isSome

/-- IsDataDescriptor (6.2.6.2). -/
def Descriptor.isData (d : Descriptor) : Bool :=
  d.value.isSome || d.writable.isSome

/-- IsGenericDescriptor (6.2.6.3): neither of the other two. -/
def Descriptor.isGeneric (d : Descriptor) : Bool :=
  !d.isAccessor && !d.isData

/-- Whether the descriptor mentions nothing at all, which 10.1.6.3 step 3
accepts outright. -/
def Descriptor.isEmpty (d : Descriptor) : Bool :=
  d.value.isNone && d.getter.isNone && d.setter.isNone &&
    d.writable.isNone && d.enumerable.isNone && d.configurable.isNone

/-- FromPropertyDescriptor's other direction: a property read as the
fully populated descriptor 6.2.6 says it is. -/
def Property.toDescriptor (p : Property) : Descriptor :=
  match p.slot with
  | .data v w =>
    { value := some v, writable := some w,
      enumerable := some p.enumerable, configurable := some p.configurable }
  | .accessor a =>
    { getter := some (a.getter.getD (.prim .undef)),
      setter := some (a.setter.getD (.prim .undef)),
      enumerable := some p.enumerable, configurable := some p.configurable }

/-- Whether a descriptor field that is present differs from the value
already there, under SameValue — 10.1.6.3's repeated test. -/
def descriptorKeeps (field : Option Value) (current : Option Value) : Bool :=
  match field with
  | none => true
  | some v => sameValueValue v (current.getD (.prim .undef))

/-- 10.1.6.3 steps 5–7 as a **predicate** on the property already there:
whether a redefinition is allowed at all. A non-configurable property
will not become configurable, will not flip its enumerability, will not
change kind, will not take a different value while non-writable, will not
become writable, and will not exchange either accessor half.

It is lifted out of `applyDescriptor` because a String exotic object's
index property is not in the property list and so has to be validated
against without being replaced: 10.4.3.5's `[[DefineOwnProperty]]` is
exactly "accept an identical redefinition, refuse anything else". -/
def Property.accepts (cur : Property) (d : Descriptor) : Bool :=
  !(!cur.configurable &&
    (d.configurable == some true ||
      (d.enumerable.isSome && d.enumerable != some cur.enumerable) ||
      (!d.isGeneric && d.isAccessor != cur.isAccessor) ||
      (match cur.slot with
       | .accessor a =>
         !(descriptorKeeps d.getter a.getter && descriptorKeeps d.setter a.setter)
       | .data v w =>
         !w && (d.writable == some true || !descriptorKeeps d.value (some v)))))

/-- `applyDescriptor` for everything that is not a String object's own
index: OrdinaryDefineOwnProperty over the property list. -/
def Obj.applyOrdinaryDescriptor (o : Obj) (key : Key) (d : Descriptor) : Option Obj :=
  match o.getOwnProperty key with
  | none =>
    if !o.extensible then none
    else
      let p : Property :=
        if d.isAccessor then
          { slot := .accessor
              { getter := accessorHalf d.getter, setter := accessorHalf d.setter },
            enumerable := d.enumerable.getD false,
            configurable := d.configurable.getD false }
        else
          { slot := .data (d.value.getD (.prim .undef)) (d.writable.getD false),
            enumerable := d.enumerable.getD false,
            configurable := d.configurable.getD false }
      some (o.define key p)
  | some cur =>
    if d.isEmpty then some o
    else
      if !cur.accepts d then none
      else
        let enumerable := d.enumerable.getD cur.enumerable
        let configurable := d.configurable.getD cur.configurable
        let slot : PropSlot :=
          match cur.slot, d.isAccessor, d.isData with
          -- A data property redefined as an accessor, and the mirror:
          -- the attributes the descriptor does not name come from the old
          -- property, but the value half starts fresh.
          | .data _ _, true, _ =>
            .accessor { getter := accessorHalf d.getter, setter := accessorHalf d.setter }
          | .accessor _, _, true => .data (d.value.getD (.prim .undef)) (d.writable.getD false)
          | .data v w, _, _ => .data (d.value.getD v) (d.writable.getD w)
          | .accessor a, _, _ =>
            .accessor
              { getter := match d.getter with | some g => accessorHalf (some g) | none => a.getter,
                setter := match d.setter with | some s => accessorHalf (some s) | none => a.setter }
        some (o.define key { slot, enumerable, configurable })

/-- ValidateAndApplyPropertyDescriptor (10.1.6.3) as a **pure function**
on an object: `none` is the specification's `false` — the change is
refused — and `some o` is the object with the property replaced or
appended.

The refusals are the table's: a non-configurable property will not
become configurable, will not flip its enumerability, will not change
kind, will not take a different value while non-writable, will not
become writable, and will not exchange either accessor half; and a key
that is not there cannot be added to a non-extensible object. An absent
field defaults to `false` or `undefined` on a new key and leaves the
existing attribute standing on an old one.

The throw belongs to the one caller that has a `TypeError` to raise, so
the whole table is `#guard`-testable without a heap
(`Test/Tarski/DescriptorTest.lean`). -/
def Obj.applyDescriptor (o : Obj) (key : Key) (d : Descriptor) : Option Obj :=
  match o.kind, key.arrayIndex? with
  -- 10.4.3.5: a String exotic object's index property is synthesized
  -- from `[[StringData]]`, so there is nothing to replace. An identical
  -- redefinition is the specification's no-op and anything else is
  -- refused.
  | .string s, some i =>
    if i < s.length then
      (if (Obj.stringIndexProperty s i).accepts d then some o else none)
    else o.applyOrdinaryDescriptor key d
  | _, _ => o.applyOrdinaryDescriptor key d

end Tarski
