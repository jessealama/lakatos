import ThalesDsl.Prove

open ThalesDsl Lean

-- A rung that simply cannot say anything must fall through to the next one.
-- Native evaluation reports its codegen and evaluation failures as ordinary
-- elaboration errors rather than runtime exceptions, so nothing in the ladder
-- catches them by default: uncontained, they escape every remaining rung and
-- become the annotation's Error.

-- A plain error is contained.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let r ← orFallThrough (α := Unit) (throwError "codegen exploded")
  return r.isNone

-- The kernel's own budget exhaustion is not: that is starvation, and only
-- runRung may classify it.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  try
    let _ ← orFallThrough (α := Unit)
      (throwError "(kernel) deterministic timeout at 'x'")
    return false
  catch _ => return true

-- Grind's own budget exhaustion is starvation too: contained inside the rung,
-- it would ship as a residual-goal GaveUp, which reads as a dead end rather
-- than as the budget it was.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let p ← Elab.Term.elabTerm (← `(∀ n : Nat, n < 5 ∨ 5 ≤ n)) (some (mkSort .zero))
  let root ← Meta.mkFreshExprMVar p
  let (outcome, starved) ←
    runRung (withHeartbeats 1 (attemptGrind ⟨"c.ts", "f", "p"⟩ p root root.mvarId! p))
  return outcome.isNone && starved

-- The real call site. A classical instance is decidable enough for `mkDecide`
-- to build the goal but noncomputable, so codegen fails inside `nativeEqTrue`
-- — the rung reports no verdict instead of taking the ladder down with it.
/-- info: true -/
#guard_msgs in
open Classical in
#eval show Elab.Term.TermElabM Bool from do
  let p ← Elab.Term.elabTerm (← `(∀ n : Nat, n < 5 ∨ 5 ≤ n)) (some (mkSort .zero))
  let r ← attemptNativeDecide ⟨"c.ts", "f", "p"⟩ p (← `((none : Option (List Int)))) []
  return r.isNone
