import Js.Binders
import ThalesDsl.Verdict

namespace ThalesDsl

/-- First witness in `[lo, hi)`, prepended to the inner witness list `f`
returns — `none` when the whole range is clean. Nesting one search per
binder builds a multi-binder witness in binder order. Fuel is the range
size, so the scan short-circuits at the first hit. -/
def findCexIco (lo hi : Int) (f : Int → Option (List WitnessValue)) :
    Option (List WitnessValue) :=
  go (hi - lo).toNat lo
where
  go : Nat → Int → Option (List WitnessValue)
    | 0, _ => none
    | n + 1, x =>
      match f x with
      | some rest => some (.int x :: rest)
      | none => go n (x + 1)

/-- The boolean binder's two values, `false` first — the order the
refuter walks, so both engines report the same witness. -/
def findCexBool (f : Bool → Option (List WitnessValue)) : Option (List WitnessValue) :=
  match f false with
  | some rest => some (.bool false :: rest)
  | none =>
    match f true with
    | some rest => some (.bool true :: rest)
    | none => none

end ThalesDsl
