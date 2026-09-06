import ThalesEmit.Render

/-! The re-parse contract, enforced at emit time: the spine
`ThalesDsl.propSpine` recovers from a printed obligation must be the one
the IR says, or the emission fails naming the obligation. -/

namespace ThalesEmit

open Lean ThalesDsl

/-- A constructor's argument heads, outermost first, ending with each
class-typed argument's own opaque instance. -/
partial def ctorSpine (path : String) (ps : Array CtorParamIR) :
    RenderM (List SpineBinder) := do
  let mut out : List SpineBinder := []
  for p in ps do
    let arg := (← fieldComponent (path ++ "." ++ p.name)).toString
    match p with
    | .number .. => out := out ++ [.unbounded arg]
    | .cls n _ _ inner _ =>
      out := out ++ (← ctorSpine (path ++ "." ++ n) inner) ++ [.opaque arg]
  return out

/-- Whether the binder's own bounds print under it as implications: a nat
binder's nonnegativity, a `number` binder's endpoints. `propSpine` stops
at the first of those, deliberately — an unbounded domain is never
searched — so nothing printed below one is recovered, this binder's
successors and the guard chain included. -/
def BinderIR.stopsSpine : BinderIR → Bool
  | .nat _ => true
  | .number _ lower upper => lower.isSome || upper.isSome
  | .range .. | .int _ | .cls .. => false

/-- The spine `propSpine` recovers from an obligation's printed binders,
named the way the renderer spells them. -/
def expectedSpine (binders : Array BinderIR) : RenderM (List SpineBinder) := do
  let mut out : List SpineBinder := []
  for b in binders do
    let name := (← scopedIdent b.name).getId.toString
    match b with
    | .range _ lo hi => out := out ++ [.ranged name lo hi]
    | .int _ | .nat _ | .number .. => out := out ++ [.unbounded name]
    | .cls _ _ _ ps => out := out ++ (← ctorSpine b.name ps) ++ [.opaque name]
    if b.stopsSpine then break
  return out

/-- The guards `propSpine` recovers: they sit under every binder, so a
binder that stops the reader leaves none of them visible. -/
def expectedGuards (binders : Array BinderIR) (guards : Nat) : Nat :=
  if binders.any BinderIR.stopsSpine then 0 else guards

private def firstDivergence : List SpineBinder → List SpineBinder → Nat → Option String
  | [], [], _ => none
  | e :: es, g :: gs, i =>
    if e == g then firstDivergence es gs (i + 1)
    else some s!"binder {i}: expected {repr e}, recovered {repr g}"
  | e :: _, [], i => some s!"binder {i}: expected {repr e}, recovered nothing"
  | [], g :: _, i => some s!"binder {i}: expected nothing, recovered {repr g}"

/-- Why a payload does not recover as expected, or `none` when it does. -/
def spineMismatch? (expected : List SpineBinder) (guardCount : Nat)
    (payload : Term) : Option String :=
  let spine := propSpine payload
  match firstDivergence expected spine.binders 0 with
  | some m => some m
  | none =>
    if spine.guards.length == guardCount then none
    else some s!"expected {guardCount} guard hypotheses, recovered {spine.guards.length}"

private def payloadOf? : Syntax → Option Term
  | `(#thales_prove $_ $_ $_ := $p:term) => some p
  | _ => none

/-- Parse a printed obligation back and hold it to its IR. Runs in the
environment the artifact will be parsed in, so what passes here parses
there. -/
def checkRoundTrip (o : Obligation) (text : String) : CoreM Unit := do
  let .structured binders guards _ := o.payload | return
  let expected ← match RenderM.run (expectedSpine binders) with
    | .error msg => throwError msg
    | .ok s => pure s
  let stx ← match Parser.runParserCategory (← getEnv) `command text with
    | .error msg =>
      throwError "obligation {o.function}/{o.property} does not re-parse: {msg}"
    | .ok stx => pure stx
  let some payload := payloadOf? stx
    | throwError "obligation {o.function}/{o.property} did not print as a #thales_prove payload"
  if let some m := spineMismatch? expected (expectedGuards binders guards.size) payload then
    throwError "obligation {o.function}/{o.property} does not round-trip through propSpine: {m}"

end ThalesEmit
