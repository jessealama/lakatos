import ThalesDsl.Binders

open Js ThalesDsl

-- ballIco decides bounded ∀ over half-open Int ranges.
#guard decide (ballIco 0 3 fun x => x < 3)
#guard !decide (ballIco 0 4 fun x => x < 3)
#guard decide (ballIco (-2) 2 fun x => x * x ≤ 4)
-- Empty range is vacuously true.
#guard decide (ballIco 5 5 fun _ => False)
-- Nested ballIco (the shape multi-binder properties elaborate to).
#guard decide (ballIco 0 5 fun a => ballIco 0 5 fun b => a + b = b + a)

-- findCexIco scans [lo, hi) for the first witness, prepending it to the
-- inner witness list.
#guard findCexIco 0 10 (fun x => if x = 3 then some [] else none) = some [3]
#guard findCexIco 0 10 (fun x => if x ≥ 3 then some [] else none) = some [3]
#guard findCexIco 0 10 (fun _ => none) = none
-- Empty range has no witness even when everything would be one.
#guard findCexIco 5 5 (fun _ => some []) = none
-- Negative bounds scan from lo.
#guard findCexIco (-3) 3 (fun x => if x * x = 4 then some [] else none) = some [-2]
-- Nested searches build multi-binder witnesses in binder order.
#guard findCexIco 0 3 (fun a => findCexIco 0 3 (fun b => if a = b then none else some []))
  = some [0, 1]
