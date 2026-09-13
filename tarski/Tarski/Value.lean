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

/-- An ordinary object: a prototype link, own data properties in
insertion order, and — for a function — the closure it calls. There are
no property descriptors and no accessors; writability, enumerability,
and getters are #389's. -/
structure Obj where
  /-- `[[Prototype]]`. `none` is the null prototype; every object here
  has one until `Object.prototype` exists (#389). -/
  proto : Option Ref := none
  /-- Own data properties, in insertion order. -/
  properties : List (String × Value) := []
  /-- `[[Call]]`. An object with one is a function. -/
  callable : Option Closure := none
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

/-- An abrupt completion — the evaluator's error channel. `break` and
`continue` are here so the monad is final; nothing in this slice builds
one. -/
inductive Completion where
  | throw (value : Value)
  | «return» (value : Value)
  | «break» (label : Option String)
  | «continue» (label : Option String)
deriving Repr, DecidableEq, Inhabited

/-- The state a program starts from. -/
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

end Tarski
