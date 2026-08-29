-- The clamp family at five guards: an isFinite throw, two -0
-- normalizations, two clamps. The arms where a normalization already fixed
-- the field leave the clamp's condition ground, so the tree the closers
-- walk prunes to a fraction of its nominal fan-out.
import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

structure TsModel.Clamp where
  x : JsNumber
  y : JsNumber

@[js_norm, grind]
def TsModel.Clamp.construct (x y : JsNumber) : JsM TsModel.Clamp := do
  let mut x := x
  let mut y := y
  if ((!Float.isFinite x) || (!Float.isFinite y)) then
    throw (JsError.error "RangeError")
  if Number.FloatOps.sameValue x (-0) then
    x := 0
  if Number.FloatOps.sameValue y (-0) then
    y := 0
  if Float.lt x 0 then
    x := 0
  if Float.lt y 0 then
    y := 0
  let «this.x» : JsNumber := x
  let «this.y» : JsNumber := y
  return TsModel.Clamp.mk «this.x» «this.y»

@[js_norm, grind]
def TsModel.Clamp.distance (self : TsModel.Clamp) (q : TsModel.Clamp) :
    JsM JsNumber := do
  let dx : JsNumber := TsModel.Clamp.x self - TsModel.Clamp.x q
  let dy : JsNumber := TsModel.Clamp.y self - TsModel.Clamp.y q
  return Float.sqrt (dx * dx + dy * dy)

#thales_prove "class-binder-clamp.ts" "Clamp#distance" "nonNegative" :=
  ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber),
    ∀ (p : TsModel.Clamp),
      TsModel.Clamp.construct «p.x» «p.y» = .ok p →
        ∀ («q.x» : JsNumber), ∀ («q.y» : JsNumber),
          ∀ (q : TsModel.Clamp),
            TsModel.Clamp.construct «q.x» «q.y» = .ok q →
              ((do return Float.le 0 (← TsModel.Clamp.distance p q)) :
                  JsM Bool) =
                pure true
