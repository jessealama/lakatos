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

/-- The spine an obligation's binders print as, named the way the
renderer spells them. -/
def expectedSpine (binders : Array BinderIR) : RenderM (List SpineBinder) := do
  let mut out : List SpineBinder := []
  for b in binders do
    let name := (← scopedIdent b.name).getId.toString
    match b with
    | .range _ lo hi => out := out ++ [.ranged name lo hi]
    | .int _ | .nat _ | .number .. => out := out ++ [.unbounded name]
    | .cls _ _ _ ps => out := out ++ (← ctorSpine b.name ps) ++ [.opaque name]
  return out

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

end ThalesEmit
