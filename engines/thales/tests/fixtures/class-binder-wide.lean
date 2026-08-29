-- One more guard than class-binder-plain.lean, on a fourth field the
-- property never reads. A guard on a dead field doubles the inversion's
-- leaf count without changing any leaf's meaning; deduplication is what
-- keeps this at the default budget.
import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

structure TsModel.Wide where
  w : JsNumber
  x : JsNumber
  y : JsNumber
  z : JsNumber

@[js_norm, grind]
def TsModel.Wide.construct (w x y z : JsNumber) : JsM TsModel.Wide := do
  let mut w := w
  let mut x := x
  let mut y := y
  let mut z := z
  if ((!Float.isFinite x) || (!Float.isFinite y)) then
    throw (JsError.error "RangeError")
  if Number.FloatOps.sameValue w (-0) then
    w := 0
  if Number.FloatOps.sameValue x (-0) then
    x := 0
  if Number.FloatOps.sameValue y (-0) then
    y := 0
  if Number.FloatOps.sameValue z (-0) then
    z := 0
  let «this.w» : JsNumber := w
  let «this.x» : JsNumber := x
  let «this.y» : JsNumber := y
  let «this.z» : JsNumber := z
  return TsModel.Wide.mk «this.w» «this.x» «this.y» «this.z»

@[js_norm, grind]
def TsModel.Wide.distance (self : TsModel.Wide) (q : TsModel.Wide) :
    JsM JsNumber := do
  let dx : JsNumber := TsModel.Wide.x self - TsModel.Wide.x q
  let dy : JsNumber := TsModel.Wide.y self - TsModel.Wide.y q
  return Float.sqrt (dx * dx + dy * dy)

#thales_prove "class-binder-wide.ts" "Wide#distance" "nonNegative" :=
  ∀ («p.w» : JsNumber), ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber),
    ∀ («p.z» : JsNumber),
      ∀ (p : TsModel.Wide),
        TsModel.Wide.construct «p.w» «p.x» «p.y» «p.z» = .ok p →
          ∀ («q.w» : JsNumber), ∀ («q.x» : JsNumber), ∀ («q.y» : JsNumber),
            ∀ («q.z» : JsNumber),
              ∀ (q : TsModel.Wide),
                TsModel.Wide.construct «q.w» «q.x» «q.y» «q.z» = .ok q →
                  ((do return Float.le 0 (← TsModel.Wide.distance p q)) :
                      JsM Bool) =
                    pure true
