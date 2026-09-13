import Tarski.Value

/-! The evaluator's monad.

`StateT Heap (ExceptT Completion Option)`: a run threads the heap, may
end abruptly with a `Completion`, and may not end at all. Divergence is
the `Option`'s `none` — it is never written by hand, because the only
thing that produces it is the bottom of the `partial_fixpoint` the
evaluator is defined by. A program that loops forever is not an error the
evaluator reports; it is a run no caller ever sees the end of, observed
only through a timeout. -/

namespace Tarski

open Js

/-- The evaluator's monad. `Option` outermost inside the transformer
stack so that divergence swallows the heap and the completion alike:
there is no partial state to inspect after a non-terminating run. -/
abbrev EvalM (α : Type) := StateT Heap (ExceptT Completion Option) α

/-- End the current run abruptly. -/
def throwCompletion {α : Type} (c : Completion) : EvalM α :=
  throw c

/-- Throw a placeholder for a runtime error whose real value is an `Error`
object this slice cannot allocate. #379 gives it a real allocation and a
prototype; no caller changes, because every caller already treats the
result as an abrupt completion and never inspects the value. -/
def throwJsError {α : Type} (kind : String) : EvalM α :=
  throwCompletion (.throw (.prim (.str kind)))

/-- Allocate a binding and answer its reference. -/
def allocCell (c : Cell) : EvalM CellRef := do
  let h ← get
  let (r, h') := h.alloc c
  set h'
  return r

/-- Read a binding. The `ReferenceError` arm is unreachable for a
reference that came out of an `Env`: the evaluator only puts references
into scope chains after allocating their cells. -/
def readCell (r : CellRef) : EvalM Cell := do
  let h ← get
  match h.read r with
  | some c => pure c
  | none => throwJsError "ReferenceError"

/-- Write a binding's value. Unreachable in the same way as `readCell`. -/
def writeCell (r : CellRef) (v : Value) : EvalM Unit := do
  modify (fun h => h.write r v)

end Tarski
