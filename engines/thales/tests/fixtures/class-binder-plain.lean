-- Hand-written pin of the class-binder obligation, on the constructor
-- shape the emitter writes: guards that throw, `-0` folded to `0`, fields
-- assigned last. The binder ranges over the constructor's image, so its
-- only finiteness is what the passed guards leave behind.
import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

structure TsModel.Point where
  x : JsNumber
  y : JsNumber

@[js_norm, grind]
def TsModel.Point.construct (x y : JsNumber) : JsM TsModel.Point := do
  let mut x := x
  let mut y := y
  if ((!Float.isFinite x) || (!Float.isFinite y)) then
    throw (JsError.error "RangeError")
  if Number.FloatOps.sameValue x (-0) then
    x := 0
  if Number.FloatOps.sameValue y (-0) then
    y := 0
  let «this.x» : JsNumber := x
  let «this.y» : JsNumber := y
  return TsModel.Point.mk «this.x» «this.y»

@[js_norm, grind]
def TsModel.Point.distance (self : TsModel.Point) (q : TsModel.Point) :
    JsM JsNumber := do
  let dx : JsNumber := TsModel.Point.x self - TsModel.Point.x q
  let dy : JsNumber := TsModel.Point.y self - TsModel.Point.y q
  return Float.sqrt (dx * dx + dy * dy)

#thales_prove "class-binder.ts" "Point#distance" "nonNegative" :=
  ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber),
    ∀ (p : TsModel.Point), TsModel.Point.construct «p.x» «p.y» = .ok p →
      ∀ («q.x» : JsNumber), ∀ («q.y» : JsNumber),
        ∀ (q : TsModel.Point), TsModel.Point.construct «q.x» «q.y» = .ok q →
          ((do return Float.le 0 (← TsModel.Point.distance p q)) : JsM Bool) =
            pure true
