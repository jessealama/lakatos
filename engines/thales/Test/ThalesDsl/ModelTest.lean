import ThalesDsl.Model

open ThalesDsl

-- Each core constructor of the pure-arithmetic slice, elaborated by ts_def
-- into a computable model under TsModel.*.

-- ts.num literal (and zero-parameter functions).
ts_def "answer" := ts.fn() : ts.number { ts.return(ts.num[42]) }
#guard decide (TsModel.answer = (pure 42.0 : TsM Float))

-- Negative literals.
ts_def "minus3" := ts.fn() : ts.number { ts.return(ts.num[-3]) }
#guard decide (TsModel.minus3 = (pure (-3.0) : TsM Float))

-- ts.id parameter references and ts.binop "+".
ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.add 2.0 3.0 = (pure 5.0 : TsM Float))

-- ts.binop "-" and "*".
ts_def "sub" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["-"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.sub 2.0 5.0 = (pure (-3.0) : TsM Float))

ts_def "sq" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}
#guard decide (TsModel.sq (-4.0) = (pure 16.0 : TsM Float))

-- ts.binop "/" — total IEEE division: finite quotients, signed infinities
-- at zero divisors, NaN at 0/0.
ts_def "ratio" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["/"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.ratio 7.0 2.0 = (pure 3.5 : TsM Float))
#guard decide (TsModel.ratio 1.0 0.0 = (pure (1.0 / 0.0) : TsM Float))
#guard decide (TsModel.ratio (-1.0) 0.0 = (pure (-(1.0 / 0.0)) : TsM Float))
#guard decide (TsModel.ratio 0.0 0.0 = (pure (0.0 / 0.0) : TsM Float))

-- ts.binop "%" — JavaScript's remainder is C fmod: the quotient truncates,
-- so the sign follows the dividend, and a zero remainder keeps that sign.
-- NaN when the dividend is infinite or the divisor zero; the dividend
-- itself when only the divisor is infinite. Pinned bit-exactly, since a
-- signed zero is invisible to `=` on Float.
ts_def "rem" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["%"](ts.id["a"], ts.id["b"]))
}

/-- The remainder's bit pattern, or `none` if the model threw. -/
def remBits (a b : Float) : Option UInt64 :=
  (TsModel.rem a b).toOption.map Float.toBits

#guard remBits 7.0 3.0 == some 0x3ff0000000000000
#guard remBits 7.5 2.0 == some 0x3ff8000000000000
#guard remBits (-7.0) 3.0 == some 0xbff0000000000000
#guard remBits 7.0 (-3.0) == some 0x3ff0000000000000
#guard remBits (-7.0) (-3.0) == some 0xbff0000000000000
#guard remBits 5.3 2.0 == some 0x3ff4cccccccccccc
-- Signed zeros: the dividend's sign survives an exact division.
#guard remBits 6.0 3.0 == some 0x0000000000000000
#guard remBits (-6.0) 3.0 == some 0x8000000000000000
#guard remBits (-0.0) 5.0 == some 0x8000000000000000
-- NaN: zero divisor, or infinite dividend.
#guard remBits 5.0 0.0 == some 0x7ff8000000000000
#guard remBits 0.0 0.0 == some 0x7ff8000000000000
#guard remBits (1.0 / 0.0) 5.0 == some 0x7ff8000000000000
#guard remBits (1.0 / 0.0) (1.0 / 0.0) == some 0x7ff8000000000000
#guard remBits (0.0 / 0.0) 5.0 == some 0x7ff8000000000000
#guard remBits 5.0 (0.0 / 0.0) == some 0x7ff8000000000000
-- An infinite divisor returns the dividend untouched.
#guard remBits 5.0 (1.0 / 0.0) == some 0x4014000000000000
#guard remBits (-5.0) (1.0 / 0.0) == some 0xc014000000000000
-- Inexact operands: the remainder is exact even when the operands are not.
#guard remBits 0.1 0.03 == some 0x3f847ae147ae1480
#guard remBits 1.0 0.1 == some 0x3fb9999999999996
#guard remBits (-1.0) 0.1 == some 0xbfb9999999999996
-- The widest exponent gap the format allows, where aligning the mantissas
-- spans the whole binary64 range.
#guard remBits (Float.ofBits 0x0000000000000001) (Float.ofBits 0x7fefffffffffffff)
  == some 0x0000000000000001
#guard remBits (Float.ofBits 0x7fefffffffffffff) (Float.ofBits 0x0000000000000001)
  == some 0x0000000000000000
#guard remBits (Float.ofBits 0x7fefffffffffffff) 3.0 == some 0x4000000000000000

-- ts.binop "**" has no model, deliberately: the language leaves
-- exponentiation implementation-approximated, so modeling it as any one
-- Float operation would certify results a conforming engine may disagree
-- with. The declaration fails, and its reason names that cause.
ts_def "power" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["**"](ts.id["x"], ts.num[2]))
}

open Lean Elab Command in
run_cmd do
  let some failed := findFailed? (← getEnv) "power"
    | throwError "'power' should have been recorded as a failed declaration"
  unless (failed.reason.splitOn "implementation-approximated").length > 1 do
    throwError "'power' failed for the wrong reason: {failed.reason}"
  unless (findModel? (← getEnv) "power").isNone do
    throwError "'power' should not have registered a model"

-- ts.call: models call previously registered models.
ts_def "twice" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.call["add"](ts.id["x"], ts.id["x"]))
}
#guard decide (TsModel.twice 7.0 = (pure 14.0 : TsM Float))

-- Nested expressions compose.
ts_def "affine" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.binop["*"](ts.num[2], ts.id["x"]), ts.num[1]))
}
#guard decide (TsModel.affine 10.0 = (pure 21.0 : TsM Float))

-- `≡` is SameValue and `===` is IEEE strict equality. They disagree on
-- exactly two families of values, and both disagreements are pinned here
-- so the two spellings can never silently re-converge.

-- A body yields a number, so `===` cannot appear at the top of one; the
-- SameValue side is pinned through models producing the contested values,
-- and the IEEE side on the primitive `===` lowers to.

-- `x * 0` is NaN at the infinities, +0 at positive x and -0 at negative x.
ts_def "zeroOver" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[0]))
}

-- SameValue, via Lean's `=` on TsM Float, which is what `ts.eq` (`≡`)
-- elaborates to: NaN *is* the same value as itself.
#guard decide (TsModel.zeroOver (1.0 / 0.0) = TsModel.zeroOver (1.0 / 0.0))
-- SameValue: +0 and -0 are different values.
#guard decide (¬ (TsModel.zeroOver 1.0 = TsModel.zeroOver (-1.0)))

-- IEEE, via `Float.beq`, which is what evalExpr lowers `===` to: NaN is
-- not strictly equal to itself, and +0 is strictly equal to -0. Both
-- disagree with SameValue above, so the two spellings cannot re-converge.
#guard decide (Float.beq (0.0 / 0.0) (0.0 / 0.0) = false)
#guard decide (Float.beq 0.0 (-0.0) = true)
