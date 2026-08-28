import ThalesDsl

open ThalesDsl Js Js.Number

/-! The non-negativity chain must close under plain `grind`: the grind
rung hands the closer nothing beyond the patterns registered in
`Js.Norm`, so an explicit lemma list here would prove the wrong thing. -/

-- The residual goal a bounded number binder leaves behind.
example : ∀ (x : JsNumber), -10 ≤ x → x ≤ 10 →
    Float.le 0 (Float.sqrt (x * x)) = true := by
  intro x hlo hhi
  grind

-- The two-coordinate distance shape, from finiteness hypotheses alone.
example (px py qx qy : Float)
    (h1 : -floatInf < px) (h2 : px < floatInf)
    (h3 : -floatInf < py) (h4 : py < floatInf)
    (h5 : -floatInf < qx) (h6 : qx < floatInf)
    (h7 : -floatInf < qy) (h8 : qy < floatInf) :
    Float.le 0 (Float.sqrt ((px - qx) * (px - qx) + (py - qy) * (py - qy))) = true := by
  grind

-- The same shape as normalization leaves it: subtraction rewritten to
-- addition of the negation, which is what a closer actually sees.
example (px py qx qy : Float)
    (h1 : -floatInf < px) (h2 : px < floatInf)
    (h3 : -floatInf < py) (h4 : py < floatInf)
    (h5 : -floatInf < qx) (h6 : qx < floatInf)
    (h7 : -floatInf < qy) (h8 : qy < floatInf) :
    Float.le 0 (Float.sqrt ((px + -qx) * (px + -qx) + (py + -qy) * (py + -qy))) = true := by
  grind

-- The bounds a class binder actually arrives with: the constructor's
-- finiteness guard, not a binder's infinity comparisons.
example (px py qx qy : Float)
    (h1 : Float.isFinite px = true) (h2 : Float.isFinite py = true)
    (h3 : Float.isFinite qx = true) (h4 : Float.isFinite qy = true) :
    Float.le 0 (Float.sqrt ((px + -qx) * (px + -qx) + (py + -qy) * (py + -qy))) = true := by
  grind
