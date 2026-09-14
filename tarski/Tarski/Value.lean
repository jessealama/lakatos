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

/-- A JS value: a primitive from the library's tagged domain, or a
reference into the heap's object table. Every primitive operation the
evaluator performs is the library's, so the primitive case carries
`JsVal` itself rather than a copy of it. -/
inductive Value where
  | prim (v : JsVal)
  | obj (ref : Ref)
deriving Repr, DecidableEq, Inhabited

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
  params : List String
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
deriving Repr, Inhabited

/-- The `Error` constructors the language has, in the order
`Tarski/Realm.lean` lays them out. `AggregateError` is absent: it takes
an iterable and has an `errors` property, neither of which this slice
can build. -/
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
  /-- `String`, called as a function: ToString of its argument. It is not
  a constructor here — the wrapper object is #391's. -/
  | stringCtor
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
deriving Repr, DecidableEq, Inhabited

/-- `[[Call]]`: user code or a built-in. -/
inductive Callable where
  | closure (c : Closure)
  | native (f : NativeFn)
deriving Repr, Inhabited

/-- How exotic an object is. `ordinary` is every object with no
internal behaviour of its own; `array` is the Array exotic object, and
its `length` lives here rather than among the properties for three
reasons: it is then never enumerated by `Object.keys`, never shadowed by
an ordinary write, and truncation is one field write rather than a scan
plus a property update. `number` and `boolean` are the Number and Boolean
wrapper objects, carrying `[[NumberData]]` and `[[BooleanData]]` the same
way — a field, not a property, so `Object.keys(new Number(1))` is empty
and no write can forge one. A kind with a `Float` in it still derives
`DecidableEq`, because propositional equality on `Float` is SameValue
(`Js/Val.lean` says so), which is the right test for a `[[NumberData]]`.
Later slices add constructors — a boxed string (#391) and `arguments`
(#393). -/
inductive ObjKind where
  | ordinary
  | array (length : Nat)
  | number (value : Float)
  | boolean (value : Bool)
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
deriving Repr, Inhabited

/-- An ordinary object: a prototype link, own data properties in
insertion order, own accessor properties beside them, and — for a
function — what calling it does. There are still no property
descriptors: writability and enumerability are #389's, which is also
what folds these two lists into one. -/
structure Obj where
  /-- `[[Prototype]]`. `none` is the null prototype; a function object's
  is one until `Function.prototype` exists (#389). -/
  proto : Option Ref := none
  /-- Own data properties, in insertion order. An array's elements are
  here, under their index keys; its `length` is not. -/
  properties : List (String × Value) := []
  /-- `[[Call]]`. An object with one is a function. -/
  callable : Option Callable := none
  /-- The exotic-object classification. Defaulted, so an ordinary
  object's literal says nothing about it. -/
  kind : ObjKind := .ordinary
  /-- Own accessor properties, in insertion order. **A key is in at most
  one of the two lists**: `Obj.defineData` and `Obj.defineAccessor` are
  the only ways in, and each drops the key from the other list first, so
  redefining a getter as a data property and back is the spec's
  replacement rather than two properties of one name. -/
  accessors : List (String × Accessor) := []
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

/-- Find a key in a property list. -/
def propGet : List (String × Value) → String → Option Value
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else propGet rest key

/-- Create or overwrite a key in a property list. An existing key keeps
its place in the insertion order; a new one goes last. -/
def propSet : List (String × Value) → String → Value → List (String × Value)
  | [], key, v => [(key, v)]
  | (k, w) :: rest, key, v =>
    if k == key then (key, v) :: rest else (k, w) :: propSet rest key v

/-- An own property's value, or `none` if the object does not have it.
Walking the prototype chain is `Eval`'s business: it may run user code
once accessors land (#389), so it cannot be a pure function of the
heap. -/
def Obj.getOwn (o : Obj) (key : String) : Option Value :=
  propGet o.properties key

/-- Create or overwrite an own property. -/
def Obj.setOwn (o : Obj) (key : String) (v : Value) : Obj :=
  { o with properties := propSet o.properties key v }

/-- Drop a key from a property list, keeping the rest in order. -/
def propDrop : List (String × Value) → String → List (String × Value)
  | [], _ => []
  | (k, v) :: rest, key => if k == key then rest else (k, v) :: propDrop rest key

/-- Find a key in an accessor list. -/
def accessorGet : List (String × Accessor) → String → Option Accessor
  | [], _ => none
  | (k, a) :: rest, key => if k == key then some a else accessorGet rest key

/-- Drop a key from an accessor list. -/
def accessorDrop : List (String × Accessor) → String → List (String × Accessor)
  | [], _ => []
  | (k, a) :: rest, key => if k == key then rest else (k, a) :: accessorDrop rest key

/-- Create or extend an accessor entry. An absent half leaves whatever is
already there standing, which is ValidateAndApplyPropertyDescriptor's own
rule: a descriptor without a `[[Set]]` field does not erase one. -/
def accessorSet : List (String × Accessor) → String → Option Value → Option Value →
    List (String × Accessor)
  | [], key, g, s => [(key, { getter := g, setter := s })]
  | (k, a) :: rest, key, g, s =>
    if k == key then
      (key, { getter := match g with | some _ => g | none => a.getter,
              setter := match s with | some _ => s | none => a.setter }) :: rest
    else (k, a) :: accessorSet rest key g s

/-- An own accessor property, or `none` if the object does not have one
under that key. -/
def Obj.getOwnAccessor (o : Obj) (key : String) : Option Accessor :=
  accessorGet o.accessors key

/-- Define an own data property. A *definition*, not a write: an accessor
of the same name is replaced rather than called, which is what makes a
class field ignore a prototype setter. -/
def Obj.defineData (o : Obj) (key : String) (v : Value) : Obj :=
  { o with accessors := accessorDrop o.accessors key,
           properties := propSet o.properties key v }

/-- Define an own accessor property, replacing a data property of the
same name and merging into an accessor already there, so that a `get x`
and a `set x` make one property with two halves. -/
def Obj.defineAccessor (o : Obj) (key : String) (getter setter : Option Value) : Obj :=
  { o with properties := propDrop o.properties key,
           accessors := accessorSet o.accessors key getter setter }

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

/-- Whether an object is an Array exotic object. -/
def Obj.isArray (o : Obj) : Bool :=
  match o.kind with
  | .array _ => true
  | _ => false

/-- `[[GetOwnProperty]]` reduced to a yes or no, which is all
`Object.prototype.hasOwnProperty` asks. An array's `length` is an own
property that lives in the kind rather than the property list, so it is
answered here by hand; an accessor property is one too, so the second
list is consulted beside the first. -/
def Obj.hasOwn (o : Obj) (key : String) : Bool :=
  match o.kind with
  | .array _ => key == "length" || (o.getOwn key).isSome || (o.getOwnAccessor key).isSome
  | _ => (o.getOwn key).isSome || (o.getOwnAccessor key).isSome

/-- ArraySetLength's shortening half: drop every element at an index at
or past the new length, keep the rest in order, and record the length.
Growing is the same operation with nothing to drop. -/
def Obj.truncate (o : Obj) (n : Nat) : Obj :=
  { o with
    kind := .array n,
    properties := o.properties.filter (fun p =>
      match arrayIndex? p.1 with
      | some i => i < n
      | none => true) }

/-- OrdinaryOwnPropertyKeys: the index keys in ascending numeric order,
then every other key in insertion order. Symbols are #392's, and an
array's `length` is not here because it is not in the property list —
`Object.keys([7, 8])` is `["0", "1"]`. Enumerability arrives with
descriptors (#389), so until then every own key is listed, accessor keys
included; they come after the data keys rather than interleaved with
them, which is an ordering limit #389 removes along with the second
list. -/
def Obj.ownKeys (o : Obj) : List String :=
  let keys := o.properties.map (·.1)
  let indexed := keys.filterMap (fun k => (arrayIndex? k).map (fun i => (i, k)))
  (indexed.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    ++ keys.filter (fun k => (arrayIndex? k).isNone)
    ++ o.accessors.map (·.1)

/-- A list of values as index-keyed properties, numbered from `start`. -/
def indexProps (start : Nat) : List Value → List (String × Value)
  | [] => []
  | v :: rest => (Nat.repr start, v) :: indexProps (start + 1) rest

/-- ArrayCreate's object: the elements under their index keys, the
length in the kind, and the given prototype. -/
def Obj.array (proto : Option Ref) (elements : List Value) : Obj :=
  { kind := .array elements.length, proto, properties := indexProps 0 elements }

end Tarski
