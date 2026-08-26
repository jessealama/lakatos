import Js.Binders

namespace ThalesDsl

/-- First witness in `[lo, hi)`, prepended to the inner witness list `f`
returns — `none` when the whole range is clean. Nesting one search per
binder builds a multi-binder witness in binder order. Fuel is the range
size, so the scan short-circuits at the first hit. -/
def findCexIco (lo hi : Int) (f : Int → Option (List Int)) : Option (List Int) :=
  go (hi - lo).toNat lo
where
  go : Nat → Int → Option (List Int)
    | 0, _ => none
    | n + 1, x =>
      match f x with
      | some rest => some (x :: rest)
      | none => go n (x + 1)

end ThalesDsl
