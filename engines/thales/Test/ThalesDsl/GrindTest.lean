import ThalesDsl

open ThalesDsl Js Js.Number

-- The grind rung shares the normalization knowledge: the js_norm
-- lemmas and model equations are tagged for grind too, so it can attack
-- goals simp never normalized (a rung-2 window blowout hands grind the
-- original proposition, monadic wrapping intact).

example (x : Int) :
    (pure x >>= fun a => pure 1 >>= fun b => pure (a + b) : JsM Int) =
      (pure (x + 1) : JsM Int) := by
  grind

-- Boolean islands discharge to their Prop for grind as for omega.
example (x : Int) (h : 0 ≤ x) :
    (pure x >>= fun a => pure 0 >>= fun b => pure (decide (a ≥ b)) : JsM Bool) =
      pure true := by
  grind

-- Bounded ∀s open up for grind.
example : ballIco 0 5 (fun x => x + 1 > x) := by
  grind

-- A ts_def model unfolds by its equations under grind.
ts_def "dblGrind" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[2]))
}

example (x : Float) : TsModel.dblGrind x = (pure (x * 2) : JsM Float) := by
  grind

-- A hardcoded factor: instantiating a monotonicity fact at a literal
-- leaves ground bound hypotheses, which discharge by kernel evaluation
-- during grind's normalization.
example (x y : Float) (hxy : Float.le x y = true) :
    Float.le (x * 3) (y * 3) = true := by
  grind

example (x y : Float) (hxy : Float.le x y = true) :
    Float.le (x / 2.54) (y / 2.54) = true := by
  grind

-- The guard chain of the four monotonicity facts: grind instantiates
-- them off the operation terms and closes the conversion shape the
-- sub-rewrite leaves behind.
example (x y sf so tf to : Float)
    (h1 : (0 : Float) < sf) (h2 : sf < floatInf)
    (h3 : -floatInf < so) (h4 : so < floatInf)
    (h5 : (0 : Float) < tf) (h6 : tf < floatInf)
    (h7 : -floatInf < to) (h8 : to < floatInf)
    (hxy : Float.le x y = true) :
    Float.le ((x * sf + so + -to) / tf) ((y * sf + so + -to) / tf) = true := by
  grind

-- Double negation strips under grind as under simp.
example (x : Float) : - -x = x := by
  grind
