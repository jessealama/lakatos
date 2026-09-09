import Js

open Js Js.Number

/-! An ordering guard feeding a difference must close under plain `grind`:
the grind rung hands the closer nothing beyond the patterns registered in
`Js.Norm`, so an explicit lemma list here would prove the wrong thing. -/

-- Self-subtraction on its own, in the spelling normalization leaves.
example (x : Float) (h1 : -floatInf < x) (h2 : x < floatInf) : x + -x = 0 := by
  grind

-- And in the source spelling: grind rewrites the subtraction itself.
example (x : Float) (h : Float.isFinite x = true) : x - x = 0 := by
  grind

-- The residual with strict bounds on the subtrahend only: the minuend's
-- finiteness is not needed, and the guard arrives as a refuted `<`-negation.
example (a b : Float)
    (h1 : -floatInf < a) (h2 : a < floatInf)
    (h3 : (!Float.le a b) = false) :
    Float.le 0 (b + -a) = true := by
  grind

-- The bounds a class binder actually arrives with: refuted infinity tests,
-- which leave NaN open until the ordering guard rules it out.
set_option linter.unusedVariables.analyzeTactics true in
example (a b : Float)
    (h1 : Float.beq a (-floatInf) = false) (h2 : Float.beq a floatInf = false)
    (h5 : Float.le a b = true) :
    Float.le 0 (b + -a) = true := by
  grind

-- The isFinite-guarded spelling, source subtraction intact: the minuend
-- needs no guard of its own.
example (a b : Float) (h1 : Float.isFinite a = true) (hab : Float.le a b = true) :
    Float.le 0 (b - a) = true := by
  grind

structure TsModel.Span where
  d : JsNumber

-- The residual a guarded constructor leaves verbatim: `||`-joined infinity
-- tests, the negated ordering guard, and the constructor-image equation.
example : ∀ («s.a» «s.b» : JsNumber) (s : TsModel.Span),
    (Float.beq «s.a» (-floatInf) || Float.beq «s.a» floatInf) = false ∧
      (Float.beq «s.b» (-floatInf) || Float.beq «s.b» floatInf) = false ∧
        (!Float.le «s.a» «s.b») = false ∧ { d := «s.b» + -«s.a» } = s →
    Float.le 0 s.d = true := by
  grind
