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

-- Fractional and scientific literals: the transcriber emits the shortest
-- round-tripping decimal, and OfScientific rounds correctly, so the token
-- reconstructs the identical double.
ts_def "cmFactor" := ts.fn() : ts.number { ts.return(ts.num[2.54]) }
#guard decide (TsModel.cmFactor = (pure 2.54 : TsM Float))

ts_def "negHalf" := ts.fn() : ts.number { ts.return(ts.num[-2.5]) }
#guard decide (TsModel.negHalf = (pure (-2.5) : TsM Float))

ts_def "sextillion" := ts.fn() : ts.number { ts.return(ts.num[1e21]) }
#guard decide (TsModel.sextillion = (pure 1e21 : TsM Float))

-- A source literal past the double range folds to the infinity it denotes.
ts_def "overflowLit" := ts.fn() : ts.number { ts.return(ts.num[Infinity]) }
#guard decide (TsModel.overflowLit = (pure floatInf : TsM Float))

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

-- ts.unop "-" is IEEE negation; "+" is ToNumber on a value already a
-- number, so it models as the identity.
ts_def "negate" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.unop["-"](ts.id["x"]))
}
#guard decide (TsModel.negate 4.0 = (pure (-4.0) : TsM Float))
-- Negation flips the sign bit even on zero.
#guard ((TsModel.negate 0.0).toOption.map Float.toBits) == some 0x8000000000000000

ts_def "posid" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.unop["+"](ts.id["x"]))
}
#guard decide (TsModel.posid (-2.5) = (pure (-2.5) : TsM Float))

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

-- Every guard above runs in the interpreter, which an `extern` would satisfy
-- too. These pin the property the model actually rests on: `tsRem` reduces in
-- the *kernel*, so the decide rung stays kernel-checked instead of falling
-- through to the evaluation tier and its axiom. One case per branch of
-- remUnpacked's dispatch.
example : (FloatOps.tsRem 7.0 3.0).toBits = 0x3ff0000000000000 := by decide
example : (FloatOps.tsRem (-6.0) 3.0).toBits = 0x8000000000000000 := by decide
example : (FloatOps.tsRem 5.0 0.0).toBits = 0x7ff8000000000000 := by decide
example : (FloatOps.tsRem 5.0 (1.0 / 0.0)).toBits = 0x4014000000000000 := by decide
example :
    (FloatOps.tsRem (Float.ofBits 0x0000000000000001)
      (Float.ofBits 0x7fefffffffffffff)).toBits = 0x0000000000000001 := by decide

-- ts.binop "**" has no model, deliberately: the language leaves
-- exponentiation implementation-approximated, so modeling it as any one
-- Float operation would certify results a conforming engine may disagree
-- with. The declaration fails naming the operator, which is what makes its
-- annotations Inappropriate — a statement about the input — rather than
-- Error, which is reserved for the engine breaking.
ts_def "power" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["**"](ts.id["x"], ts.num[2]))
}

open Lean Elab Command in
run_cmd do
  let some failed := findFailed? (← getEnv) "power"
    | throwError "'power' should have been recorded as a failed declaration"
  unless failed.construct == some "**" do
    throwError "'power' must name the refused operator, got {repr failed.construct}"
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

-- ts.const bindings: straight-line, each visible to later initializers
-- and the return; elaborated as binds, so evaluation order is preserved.
ts_def "affineConst" := ts.fn(ts.param["n"](ts.number)) : ts.number {
  ts.const["doubled"](ts.binop["*"](ts.num[2], ts.id["n"]))
  ts.const["shifted"](ts.binop["+"](ts.id["doubled"], ts.num[2]))
  ts.return(ts.id["shifted"])
}
#guard decide (TsModel.affineConst 3.0 = (pure 8.0 : TsM Float))

-- A binding may go unused; its initializer still elaborates.
ts_def "ignored" := ts.fn(ts.param["a"](ts.number)) : ts.number {
  ts.const["unused"](ts.binop["/"](ts.id["a"], ts.num[0]))
  ts.return(ts.id["a"])
}
#guard decide (TsModel.ignored 4.0 = (pure 4.0 : TsM Float))

-- A use before its binding is an unbound identifier, contained per decl.
ts_def "tdz" := ts.fn() : ts.number {
  ts.const["a"](ts.id["b"])
  ts.const["b"](ts.num[1])
  ts.return(ts.id["a"])
}

-- A binding after the return violates the body shape, contained per decl.
ts_def "deadTail" := ts.fn() : ts.number {
  ts.return(ts.num[1])
  ts.const["x"](ts.num[2])
}

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  unless (findModel? env "affineConst").isSome do
    throwError "'affineConst' should register a model"
  let some tdz := findFailed? env "tdz"
    | throwError "'tdz' should be recorded as failed"
  unless tdz.construct == none do
    throwError "'tdz' is not an opaque failure, got {repr tdz.construct}"
  let some dead := findFailed? env "deadTail"
    | throwError "'deadTail' should be recorded as failed"
  unless dead.construct == none do
    throwError "'deadTail' is not an opaque failure, got {repr dead.construct}"
