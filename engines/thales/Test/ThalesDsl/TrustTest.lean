import ThalesDsl.Prove

open ThalesDsl Lean

-- The two tiers must not rest on the same thing, and `provedVerdict` decides
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

-- The verdict line names those axioms: none for a kernel proof, and for an
-- evaluated proof the admitted per-theorem one under its canonical spelling —
-- detected off the theorem rather than asserted, but never reported under the
-- generated name, which carries the module path and an elaboration counter.
-- (Compressed JSON orders keys alphabetically, so `axioms` leads.)
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let v ← provedVerdict ⟨"f.ts", "f", "p"⟩ "a decision procedure" ``kernelTier
  return v.toJson.compress.startsWith "{\"axioms\":[],"

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let v ← provedVerdict ⟨"f.ts", "f", "p"⟩ "a decision procedure" ``nativeTier
  return v.toJson.compress.startsWith
    "{\"axioms\":[\"Lean.ofReduceBool\"],"

-- The canonicalization keys on the name's shape, not on any one counter,
-- and leaves every other axiom alone.
/-- info: true -/
#guard_msgs in
#eval [canonicalAxiom `nativeTier._native.native_decide.ax_1_1,
       canonicalAxiom (`_private.tests.fixtures |>.str "theorem-arith" |>.num 0
         |>.str "_native" |>.str "native_decide" |>.str "ax_15"),
       canonicalAxiom ``propext,
       canonicalAxiom `_native.native_decide.decl_3]
    == [``Lean.ofReduceBool, ``Lean.ofReduceBool, ``propext,
        `_native.native_decide.decl_3]
