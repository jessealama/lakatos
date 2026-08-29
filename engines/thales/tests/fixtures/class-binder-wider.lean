-- Seven guards over two binders: two more fields than
-- class-binder-wide.lean, each with its own normalization. Splitting the
-- constructor image on every guard put this past any budget, so the shape
-- pins that the facts are read off the image rather than split out of it.
import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

structure TsModel.Wide where
  u : JsNumber
  v : JsNumber
  w : JsNumber
  x : JsNumber
  y : JsNumber
  z : JsNumber

@[js_norm, grind]
def TsModel.Wide.construct (u v w x y z : JsNumber) : JsM TsModel.Wide := do
  let mut u := u
  let mut v := v
  let mut w := w
  let mut x := x
  let mut y := y
  let mut z := z
  if ((!Float.isFinite x) || (!Float.isFinite y)) then
    throw (JsError.error "RangeError")
  if Number.FloatOps.sameValue u (-0) then
    u := 0
  if Number.FloatOps.sameValue v (-0) then
    v := 0
  if Number.FloatOps.sameValue w (-0) then
    w := 0
  if Number.FloatOps.sameValue x (-0) then
    x := 0
  if Number.FloatOps.sameValue y (-0) then
    y := 0
  if Number.FloatOps.sameValue z (-0) then
    z := 0
  let «this.u» : JsNumber := u
  let «this.v» : JsNumber := v
  let «this.w» : JsNumber := w
  let «this.x» : JsNumber := x
  let «this.y» : JsNumber := y
  let «this.z» : JsNumber := z
  return TsModel.Wide.mk «this.u» «this.v» «this.w» «this.x» «this.y» «this.z»

@[js_norm, grind]
def TsModel.Wide.distance (self : TsModel.Wide) (q : TsModel.Wide) :
    JsM JsNumber := do
  let dx : JsNumber := TsModel.Wide.x self - TsModel.Wide.x q
  let dy : JsNumber := TsModel.Wide.y self - TsModel.Wide.y q
  return Float.sqrt (dx * dx + dy * dy)

#thales_prove "class-binder-wider.ts" "Wide#distance" "nonNegative" :=
  ∀ («p.u» : JsNumber), ∀ («p.v» : JsNumber), ∀ («p.w» : JsNumber),
    ∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber), ∀ («p.z» : JsNumber),
      ∀ (p : TsModel.Wide),
        TsModel.Wide.construct «p.u» «p.v» «p.w» «p.x» «p.y» «p.z» = .ok p →
          ∀ («q.u» : JsNumber), ∀ («q.v» : JsNumber), ∀ («q.w» : JsNumber),
            ∀ («q.x» : JsNumber), ∀ («q.y» : JsNumber), ∀ («q.z» : JsNumber),
              ∀ (q : TsModel.Wide),
                TsModel.Wide.construct «q.u» «q.v» «q.w» «q.x» «q.y» «q.z» =
                    .ok q →
                  ((do return Float.le 0 (← TsModel.Wide.distance p q)) :
                      JsM Bool) =
                    pure true
