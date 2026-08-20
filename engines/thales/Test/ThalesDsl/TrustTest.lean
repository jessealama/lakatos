import ThalesDsl.Prove

open ThalesDsl Lean

-- The two tiers must not rest on the same thing, and `proofReason` decides
-- which by reading the theorem's axioms. Pin both directions against real
-- proofs rather than against the wording of any reason string.

theorem kernelTier : (2.0 : Float) + 3.0 = 5.0 := by decide
theorem nativeTier : ((List.range 40).all fun n =>
    let x : Float := n.toFloat
    (x * 2.0) == (x + x)) = true := by native_decide

-- A kernel proof uses nothing beyond the standard axioms.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``kernelTier
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

-- A natively evaluated proof carries an extra one; that is the whole
-- difference the verdict has to report.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``nativeTier
  return !(axioms.filter (!standardAxioms.contains ·)).isEmpty
