import ThalesDsl.Binders

open ThalesDsl

-- findCexIco scans [lo, hi) for the first witness, prepending it to the
-- inner witness list.
#guard findCexIco 0 10 (fun x => if x = 3 then some [] else none) = some [.int 3]
#guard findCexIco 0 10 (fun x => if x ≥ 3 then some [] else none) = some [.int 3]
#guard findCexIco 0 10 (fun _ => none) = none
-- Empty range has no witness even when everything would be one.
#guard findCexIco 5 5 (fun _ => some []) = none
-- Negative bounds scan from lo.
#guard findCexIco (-3) 3 (fun x => if x * x = 4 then some [] else none) = some [.int (-2)]
-- Nested searches build multi-binder witnesses in binder order.
#guard findCexIco 0 3 (fun a => findCexIco 0 3 (fun b => if a = b then none else some []))
  = some [.int 0, .int 1]
-- findCexBool tries false before true, the order the refuter walks.
#guard findCexBool (fun b => if b then some [] else none) = some [.bool true]
#guard findCexBool (fun b => if b then none else some []) = some [.bool false]
#guard findCexBool (fun _ => some []) = some [.bool false]
#guard findCexBool (fun _ => none) = none
-- A mixed spine nests the same way.
#guard findCexIco 0 3 (fun n => findCexBool (fun b => if b || n = 0 then none else some []))
  = some [.int 1, .bool false]
