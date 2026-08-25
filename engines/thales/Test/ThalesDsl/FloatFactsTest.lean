import Js.Number.FloatFacts
import ThalesDsl.Prove

open ThalesDsl Lean Js Js.Number
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

-- The reverse direction: packing a word's own unpacking gives the word
-- back. Validity is the whole hypothesis — it rules out the one bit
-- pattern that does not survive, a non-canonical `NaN` payload.
example (b : BitVec Format.binary64.numBits) (hv : Format.binary64.Valid b) :
    UnpackedFloat.pack .binary64 (unpack .binary64 b) = b :=
  FloatFacts.pack_unpack_of_valid hv

example (f : Float.Model) : Float.Model.pack f.unpack = f :=
  FloatFacts.model_pack_unpack f

-- Kernel-computed pins on the branches the general lemma splits on:
-- infinity, canonical NaN, zero, subnormal, normal.
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0x7ff0000000000000#64)) =
    0x7ff0000000000000#64 := rfl
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0x7ff8000000000000#64)) =
    0x7ff8000000000000#64 := rfl
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0x8000000000000000#64)) =
    0x8000000000000000#64 := rfl
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0x0000000000000001#64)) =
    0x0000000000000001#64 := rfl
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0xbff8000000000000#64)) =
    0xbff8000000000000#64 := rfl

-- A non-canonical `NaN` is exactly what the hypothesis excludes: it
-- unpacks to `.notANumber` and repacks to the canonical payload.
example : UnpackedFloat.pack .binary64 (unpack .binary64 (0x7ff0000000000001#64)) =
    0x7ff8000000000000#64 := rfl

-- The lifted facts themselves, at the layer residual goals are stated in.
example (a b : Float) : a - b = a + (-b) := FloatFacts.float_sub_eq_add_neg a b

example (a : Float) : - -a = a := FloatFacts.float_neg_neg a

-- It is a proof, not an assumption: a verdict resting on it still reports
-- an empty `axioms` array.
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

-- The four monotonicity facts at the Float layer: the shapes residual
-- goals state them in, one application each, plus the bound flips the
-- sub-rewrite needs.
example (x y c : Float) (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < (1.0 / 0.0 : Float)) :
    Float.le (x * c) (y * c) = true :=
  FloatFacts.float_le_mul_right h h0 hInf

example (x y c : Float) (h : Float.le x y = true)
    (hLo : (-(1.0 / 0.0) : Float) < c) (hHi : c < (1.0 / 0.0 : Float)) :
    Float.le (x + c) (y + c) = true :=
  FloatFacts.float_le_add_right h hLo hHi

example (x y c : Float) (h : Float.le x y = true)
    (hLo : (-(1.0 / 0.0) : Float) < c) (hHi : c < (1.0 / 0.0 : Float)) :
    Float.le (x - c) (y - c) = true :=
  FloatFacts.float_le_sub_right h hLo hHi

example (x y c : Float) (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < (1.0 / 0.0 : Float)) :
    Float.le (x / c) (y / c) = true :=
  FloatFacts.float_le_div_right h h0 hInf

example (c : Float) (h : c < (1.0 / 0.0 : Float)) : (-(1.0 / 0.0) : Float) < -c :=
  FloatFacts.float_neg_bound_lo h

example (c : Float) (h : (-(1.0 / 0.0) : Float) < c) : -c < (1.0 / 0.0 : Float) :=
  FloatFacts.float_neg_bound_hi h

-- Kernel-computed instances, one per operation, with a negative operand
-- and an overflow-free subnormal in the mix.
example : Float.le (-3.5 * 2.0) (1.25 * 2.0) = true :=
  FloatFacts.float_le_mul_right rfl rfl rfl

example : Float.le (-3.5 + 0.5) (1.25 + 0.5) = true :=
  FloatFacts.float_le_add_right rfl rfl rfl

example : Float.le (-3.5 - 0.5) (1.25 - 0.5) = true :=
  FloatFacts.float_le_sub_right rfl rfl rfl

example : Float.le (-3.5 / 2.0) (1.25 / 2.0) = true :=
  FloatFacts.float_le_div_right rfl rfl rfl
