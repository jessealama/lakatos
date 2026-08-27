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

/-! The converse direction: a class binder has no range, so its
finiteness comes only from the negated constructor guards. Each bridge
pinned by application, then the pipeline shape under plain `grind`. -/

example (x : Float) (hn : x.toModel.unpack ≠ .notANumber)
    (h : Float.beq x floatInf = false) : x < floatInf :=
  float_lt_inf_of_beq_false hn h

example (x : Float) (hn : x.toModel.unpack ≠ .notANumber)
    (h : Float.beq x (-floatInf) = false) : -floatInf < x :=
  float_gt_neg_inf_of_beq_false hn h

example (x : Float) (h : Number.FloatOps.sameValue x floatNaN = false) :
    x.toModel.unpack ≠ .notANumber :=
  unpack_ne_nan_of_sameValue_false h

-- Exactly the hypotheses a successful constructor leaves behind: negated
-- guards, no range. grind splits the `||` and chains the bridges itself.
example (x : Float)
    (hInf : (Float.beq x (-floatInf) || Float.beq x floatInf) = false)
    (hNan : Number.FloatOps.sameValue x floatNaN = false) :
    -floatInf < x ∧ x < floatInf := by
  grind

/-! A passed comparison guard refutes the throwing arm's own comparison —
the direction a class constructor needs, where the surviving branch is
what the annotation quantifies over. -/

example (x : Float) (h : Float.le 0 x = true) : Float.lt x 0 = false :=
  float_lt_eq_false_of_le h

-- The constructor shape: the guard hypothesis alone must kill the
-- throwing arm, since no pure result equals a throw.
example : ∀ (a : JsNumber),
    Float.le 0 a = true →
      (do
          let __do_lift ←
            if Float.lt a 0 = true then do
                throw (JsError.error "RangeError")
                pure 0
              else pure a
          pure __do_lift) =
        (pure a : JsM JsNumber) := by
  intro a h
  grind
