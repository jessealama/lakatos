import Js.Val

/-! The value domain, the heap, environments, and completions.

The shapes here are fixed now, before anything needs them, so that later
slices extend rather than rewrite. This slice allocates no object and
produces no abrupt completion but `throw`; `Obj`, `Completion.return`,
`.break`, and `.continue` are nonetheless part of the domain, because the
evaluator that grows into functions and labelled loops should not change
its state type to get them.

Bindings live in the heap, not in the environment, for two reasons: an
assignment inside a `while` body must be visible after the loop, and a
closure (#378) captures an `Env` by value while still seeing later writes
to the cells it names. -/

namespace Tarski

open Js

-- The library derives `Repr` on `JsVal` but not `DecidableEq`, having no
-- use for it; the evaluator's tests compare whole results, so derive it
-- here rather than give the library an instance it does not need.
deriving instance DecidableEq for JsVal

/-- An object's identity. Nothing in this slice allocates one. -/
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

/-- An object. A placeholder: #378 gives it properties, a prototype, and
a callable slot. It exists now so `Heap` has its final shape. -/
structure Obj where
  /-- Own properties, in insertion order. Always empty in this slice. -/
  properties : List (String × Value) := []
deriving Repr, DecidableEq, Inhabited

/-- A variable binding. `mutable` is `false` for `const`, which is what
makes assignment to a `const` a runtime refusal rather than a silent
write. #393 makes `value` optional to model the temporal dead zone; that
is a field change, not a reshaping. -/
structure Cell where
  mutable : Bool
  value : Value
deriving Repr, DecidableEq, Inhabited

/-- The mutable state of a run: variable bindings and objects. -/
structure Heap where
  cells : Array Cell := #[]
  objects : Array Obj := #[]
deriving Repr, DecidableEq, Inhabited

/-- A scope chain, innermost first. Lookup takes the first match, so a
block's binding shadows an outer one of the same name without any
deletion. -/
abbrev Env := List (String × CellRef)

/-- An abrupt completion — the evaluator's error channel. Only `throw`
occurs in this slice; the rest are here so the monad is final. -/
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
  | some c => { h with cells := h.cells.set! r { c with value := v } }
  | none => h

/-- Resolve a name in a scope chain: the innermost binding wins. -/
def Env.lookup : Env → String → Option CellRef
  | [], _ => none
  | (n, r) :: rest, name => if n == name then some r else Env.lookup rest name

end Tarski
