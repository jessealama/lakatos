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

/-- Whether a function has a `this` of its own. An arrow does not: it
pushes no `this` binding, so `this` inside it resolves up the scope chain
like any other name, which is the spec's own mechanism. -/
inductive FuncKind where
  | ordinary
  | arrow
deriving Repr, DecidableEq, Inhabited

/-- A function's code and the scope it closed over. -/
structure Closure where
  params : List String
  body : List Stmt
  env : Env
  kind : FuncKind
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

/-- An ordinary object: a prototype link, own data properties in
insertion order, and — for a function — what calling it does. There are
no property descriptors and no accessors; writability, enumerability,
and getters are #389's. -/
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
answered here by hand. -/
def Obj.hasOwn (o : Obj) (key : String) : Bool :=
  match o.kind with
  | .array _ => key == "length" || (o.getOwn key).isSome
  | _ => (o.getOwn key).isSome

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
descriptors (#389), so until then every own key is listed. -/
def Obj.ownKeys (o : Obj) : List String :=
  let keys := o.properties.map (·.1)
  let indexed := keys.filterMap (fun k => (arrayIndex? k).map (fun i => (i, k)))
  (indexed.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    ++ keys.filter (fun k => (arrayIndex? k).isNone)

/-- A list of values as index-keyed properties, numbered from `start`. -/
def indexProps (start : Nat) : List Value → List (String × Value)
  | [] => []
  | v :: rest => (Nat.repr start, v) :: indexProps (start + 1) rest

/-- ArrayCreate's object: the elements under their index keys, the
length in the kind, and the given prototype. -/
def Obj.array (proto : Option Ref) (elements : List Value) : Obj :=
  { kind := .array elements.length, proto, properties := indexProps 0 elements }

end Tarski
