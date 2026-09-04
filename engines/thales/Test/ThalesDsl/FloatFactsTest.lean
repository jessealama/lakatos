import Js.Number.FloatFacts
import ThalesDsl.Prove

open ThalesDsl Lean Js Js.Number

-- The lifted binary64 facts are proofs, not assumptions: a verdict resting
-- on any of them still reports an empty `axioms` array. Their content is
-- pinned in `Test/Js/FloatFactsTest.lean`; this is the trust side.

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_sub_eq_add_neg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_neg_neg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

-- The whole non-negativity chain kernel-checks the same way.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_sub_ne_nan
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_sq_nonneg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_add_nonneg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty

/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_sqrt_nonneg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty
