import Tarski.Realm

/-! The evaluator's monad.

`ExceptT Completion (StateT Heap Option)`: a run threads the heap, may
end abruptly with a `Completion`, and may not end at all. Divergence is
the `Option`'s `none` — it is never written by hand, because the only
thing that produces it is the bottom of the `partial_fixpoint` the
evaluator is defined by. A program that loops forever is not an error the
evaluator reports; it is a run no caller ever sees the end of, observed
only through a timeout.

The order of the two transformers is the whole of the design. Unfolded,
this stack is `Heap → Option (Except Completion α × Heap)`: an abrupt
completion carries the heap out beside it, so catching one keeps every
write the abrupt part performed. The other order,
`StateT Heap (ExceptT Completion Option)`, is
`Heap → Option (Except Completion (α × Heap))`, which pairs the heap with
the *value* and therefore drops it on the error side: a function's own
`return` would undo the function's writes, and a `catch` would roll the
heap back, neither of which JavaScript does. Divergence still swallows
both, because the `Option` is outside both of them.

`partial_fixpoint` has no monotonicity lemma for `tryCatch`, so a
recursive definition may not catch inline. Catching is instead an opaque
definition here with its own `@[partial_fixpoint_monotone]` lemma, and
there are exactly two: `catchReturn`, which a call site wraps its body
in, and `attempt`, which *reifies* a completion rather than choosing one
shape to swallow. Every other catch — a `try`, a `finally`, a loop's
`break`, a label's — is an ordinary `match` on what `attempt` answered,
inside the fixpoint block, needing no lemma of its own because
`partial_fixpoint` already handles a `match`. One shape, one lemma, and a
catching arm may recurse. -/

namespace Tarski

open Js

/-- The evaluator's monad. `Option` outermost inside the transformer
stack so that divergence swallows the heap and the completion alike:
there is no partial state to inspect after a non-terminating run. -/
abbrev EvalM (α : Type) := ExceptT Completion (StateT Heap Option) α

/-- End the current run abruptly. -/
def throwCompletion {α : Type} (c : Completion) : EvalM α :=
  throw c

/-- Catch a `return` completion, letting every other one through. Opaque
on purpose: `partial_fixpoint` cannot eliminate a recursive call written
under `tryCatch`, but it can see through this definition given the
monotonicity lemma below. -/
def catchReturn (x : EvalM Value) : EvalM Value :=
  ExceptT.mk do
    match ← x.run with
    | .ok v => pure (.ok v)
    | .error (.«return» v) => pure (.ok v)
    | .error c => pure (.error c)

open Lean.Order in
/-- `catchReturn` is monotone in its argument, which is what lets a
recursive definition call itself under it. -/
@[partial_fixpoint_monotone]
theorem monotone_catchReturn {γ : Type} [PartialOrder γ] (f : γ → EvalM Value)
    (hmono : monotone f) : monotone (fun x => catchReturn (f x)) := by
  unfold catchReturn
  apply monotone_bind
  · exact hmono
  · apply monotone_const

/-- Run a computation and answer its completion as a value: `.ok` for a
normal one, `.error c` for an abrupt one. Nothing is swallowed — the
caller decides, by an ordinary `match`, which completions it handles and
rethrows the rest with `throwCompletion`. The heap comes out either way,
because the state is inside the `Except`, so a caught throw keeps every
write the abrupt part made.

Opaque for the same reason `catchReturn` is: `partial_fixpoint` cannot
eliminate a recursive call written under `tryCatch`, but it can see
through this definition given the monotonicity lemma below, and the
`match` that follows is one it already handles. -/
def attempt {α : Type} (x : EvalM α) : EvalM (Except Completion α) :=
  ExceptT.mk do
    let r ← x.run
    pure (.ok r)

open Lean.Order in
/-- `attempt` is monotone in its argument, which is what lets a
recursive definition call itself under it — and, since the `match` on its
answer is ordinary, lets a catching arm recurse too. -/
@[partial_fixpoint_monotone]
theorem monotone_attempt {α γ : Type} [PartialOrder γ] (f : γ → EvalM α)
    (hmono : monotone f) : monotone (fun x => attempt (f x)) := by
  unfold attempt
  apply monotone_bind
  · exact hmono
  · apply monotone_const

/-! ### Running the stack under `simp`

A proof about a closed program reduces `((x.run).run h)`, and for that
`simp` has to push `ExceptT.run` through every bind and every state
operation. Core tags `StateT.run_bind` as `simp` but not
`ExceptT.run_bind`, so a proof adds that one lemma to its set by hand
(with `Except.map`, which the `Functor` arm of a `do` block leaves
behind); the three below supply what core has no lemma for at all,
namely `ExceptT.run` of the lifted state operations. They are stated with
`StateT.mk` on the right so that `StateT.run_mk` takes it from there. -/

@[simp] theorem run_get :
    (get : EvalM Heap).run = StateT.mk (fun h => some (Except.ok h, h)) := rfl

@[simp] theorem run_set (h₀ : Heap) :
    (set h₀ : EvalM PUnit).run = StateT.mk (fun _ => some (Except.ok ⟨⟩, h₀)) := rfl

@[simp] theorem run_modify (f : Heap → Heap) :
    (modify f : EvalM PUnit).run = StateT.mk (fun h => some (Except.ok ⟨⟩, f h)) := rfl

/-- Allocate an object and answer its reference. -/
def allocObj (o : Obj) : EvalM Ref := do
  let h ← get
  let (r, h') := h.allocObj o
  set h'
  return r

/-- OrdinaryObjectCreate against `%Object.prototype%`: the object an
object literal, a function's `prototype`, and `Object()` all start
from. -/
def newObject : EvalM Ref :=
  allocObj { proto := some objectProtoRef }

/-- ArrayCreate: a fresh array holding the given elements, linked to
`%Array.prototype%`. -/
def newArray (elements : List Value) : EvalM Value := do
  pure (.obj (← allocObj (Obj.array (some arrayProtoRef) elements)))

/-- ArrayCreate with a length and no elements — `Array(n)`'s answer, an
array of `n` holes, every index of which reads `undefined` off the empty
property list. -/
def newArrayOfLength (n : Nat) : EvalM Value := do
  pure (.obj (← allocObj { proto := some arrayProtoRef, kind := .array n }))

/-- Throw one of the evaluator's own runtime errors: a fresh object whose
prototype is the kind's, carrying the message as an own property. The
`name` it will report comes from that prototype, so the object is exactly
what `new TypeError(message)` builds, which is what makes the evaluator's
refusals catchable and testable with `instanceof`.

Every message the evaluator raises is in one table in `Tarski/Eval.lean`'s
header. test262 never inspects them; the table exists so the tests can
pin what the binary prints. -/
def throwJsError {α : Type} (kind : ErrorKind) (message : String) : EvalM α := do
  let r ← allocObj
    { proto := some kind.protoRef, properties := [("message", .prim (.str message))] }
  throwCompletion (.throw (.obj r))

/-- Allocate a binding and answer its reference. -/
def allocCell (c : Cell) : EvalM CellRef := do
  let h ← get
  let (r, h') := h.alloc c
  set h'
  return r

/-- The cell a reference names. The error arm is unreachable for a
reference that came out of an `Env`: the evaluator only puts references
into scope chains after allocating their cells. -/
def getCell (r : CellRef) : EvalM Cell := do
  let h ← get
  match h.read r with
  | some c => pure c
  | none => throwJsError .referenceError "dangling binding"

/-- Read a binding's value. An uninitialized cell is a name in its
temporal dead zone — in scope, because its block was instantiated, but
not yet reached by its declarator — and reading one is a
`ReferenceError`, which is what makes the TDZ observable. The name is
passed in so the message can say which binding it was. -/
def readCell (name : String) (r : CellRef) : EvalM Value := do
  match (← getCell r).value with
  | some v => pure v
  | none => throwJsError .referenceError s!"Cannot access '{name}' before initialization"

/-- Write a binding's value. -/
def writeCell (r : CellRef) (v : Value) : EvalM Unit := do
  modify (fun h => h.write r v)

/-- End a binding's temporal dead zone. The same operation as
`writeCell`, under the name the spec gives it: initializing a cell and
assigning to one are different events even where the code is one, and
`#393`'s `var` will initialize without any declarator having run. -/
def initCell (r : CellRef) (v : Value) : EvalM Unit :=
  writeCell r v

/-- The object a reference names. Unreachable in the same way as
`getCell`: a `Value.obj` only ever holds a reference the heap handed
out. -/
def readObj (r : Ref) : EvalM Obj := do
  let h ← get
  match h.readObj r with
  | some o => pure o
  | none => throwJsError .typeError "dangling object"

/-- Replace an object. -/
def writeObj (r : Ref) (o : Obj) : EvalM Unit := do
  modify (fun h => h.writeObj r o)

/-- Read an object, transform it, and write it back. -/
def modifyObj (r : Ref) (f : Obj → Obj) : EvalM Unit := do
  writeObj r (f (← readObj r))

end Tarski
