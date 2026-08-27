import ThalesDsl

open ThalesDsl Js Js.Number

/-! Guard refutation must close under plain `grind`: the grind rung hands
the closer nothing beyond the patterns registered in `Js.Norm`, so an
explicit lemma list here would prove the wrong thing. -/

-- The residual a guarded sqrt leaves behind: the throwing arm's condition
-- is refuted by the binder's bounds, the surviving arm is the chain.
example : ∀ (x : JsNumber),
    -10 ≤ x →
      x ≤ 10 →
        (do
            let __do_lift ←
              if (Float.beq x (-floatInf) || Float.beq x floatInf) = true then do
                  throw (JsError.error "RangeError")
                  pure (Float.sqrt (x * x))
                else pure (Float.sqrt (x * x))
            pure (Float.le 0 __do_lift)) =
          (pure true : JsM Bool) := by
  intro x h1 h2
  grind

-- The same with the NaN guard a constructor writes next to the infinity
-- one.
example : ∀ (x : JsNumber),
    -10 ≤ x →
      x ≤ 10 →
        (do
            let __do_lift ←
              if Number.FloatOps.sameValue x floatNaN = true then do
                  throw (JsError.error "RangeError")
                  pure (Float.sqrt (x * x))
                else pure (Float.sqrt (x * x))
            pure (Float.le 0 __do_lift)) =
          (pure true : JsM Bool) := by
  intro x h1 h2
  grind

-- Two sequential guards, each its own statement: the do-elaborator nests
-- the conditions, and each arm still refutes from the bounds alone.
example : ∀ (x : JsNumber),
    -10 ≤ x →
      x ≤ 10 →
        (do
            if Number.FloatOps.sameValue x floatNaN = true then
              throw (JsError.error "RangeError")
            if (Float.beq x (-floatInf) || Float.beq x floatInf) = true then
              throw (JsError.error "RangeError")
            let __do_lift ← pure (Float.sqrt (x * x))
            pure (Float.le 0 __do_lift)) =
          (pure true : JsM Bool) := by
  intro x h1 h2
  grind
