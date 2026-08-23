import ThalesDsl.FloatFacts
import ThalesDsl.Prove

open ThalesDsl Lean
open Float.Model Float.Model.UnpackedFloat

-- The bridge from `UnpackedFloat` theory to a `Float` goal is the
-- pack/unpack round-trip. Pin it on each canonical shape, since the
-- general lemma's case split is where it can silently go wrong.

example : FloatFacts.Canonical .notANumber := .notANumber
example : FloatFacts.Canonical (.infinity .negative) := .infinity _
example : FloatFacts.Canonical (.zero .negative) := .zero _

example (b : BitVec Format.binary64.numBits) :
    unpack .binary64 (UnpackedFloat.pack .binary64 (unpack .binary64 b)) = unpack .binary64 b :=
  FloatFacts.unpack_pack_of_canonical (FloatFacts.canonical_unpack b)

-- The subnormal band and the normal band are the two the general lemma
-- proves rather than reduces; check one representative of each.
example : unpack .binary64 (UnpackedFloat.pack .binary64
    (.finite .negative 1 (-1074) (by omega))) = .finite .negative 1 (-1074) (by omega) :=
  FloatFacts.unpack_pack_of_canonical (.subnormal _ _ (by omega) (by omega))

example : unpack .binary64 (UnpackedFloat.pack .binary64
    (.finite .negative (2 ^ 52) 0 (by omega))) = .finite .negative (2 ^ 52) 0 (by omega) :=
  FloatFacts.unpack_pack_of_canonical (.normal _ _ _ (by omega) (by omega) (by omega)
    (by omega) (by omega))

-- Negation stays inside the canonical set, which is what lets a negated
-- operand survive being repacked.
example (f : Float.Model) : (Float.Model.pack f.unpack.neg).unpack = f.unpack.neg :=
  FloatFacts.model_unpack_pack_neg f

-- The lifted fact itself, at the layer residual goals are stated in.
example (a b : Float) : a - b = a + (-b) := FloatFacts.float_sub_eq_add_neg a b

-- It is a proof, not an assumption: a verdict resting on it still reports
-- an empty `axioms` array.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from do
  let axioms ← collectAxioms ``FloatFacts.float_sub_eq_add_neg
  return (axioms.filter (!standardAxioms.contains ·)).isEmpty
