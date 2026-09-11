import ThalesDsl

open Js ThalesDsl Lean

/-! The prover's reading of a residual: an opaque this artifact declared,
found in a failing leaf, names its construct; a leaf that fails for any
other reason keeps the GaveUp. The verdict line itself is pinned by the
channel check over `tests/fixtures/residual.lean`. -/

/-- 'Math.log' is not supported -/
noncomputable opaque TsModel.f.residual_1 : (x : JsNumber) → JsM JsNumber

@[js_norm, grind]
noncomputable def TsModel.f (x : JsNumber) : JsM JsNumber := do
  if Float.lt x 0 then
    return (← TsModel.f.residual_1 x)
  return x

/-- The grind rung's verdict on a proposition, called as the ladder calls
it. -/
def grindOn (stx : TSyntax `term) : Elab.Term.TermElabM Verdict := do
  let p ← Elab.Term.elabTerm stx (some (mkSort .zero))
  let root ← Meta.mkFreshExprMVar p
  attemptGrind ⟨"r.ts", "f", "p"⟩ p root root.mvarId! p

-- On-path: the guard selects the residual arm and refutes the other, so the
-- residual leaf is the only failure and its docstring reaches the verdict.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let v ← grindOn (← `(∀ (x : JsNumber), Float.lt x 0 = true →
    ((do return Float.le 0 (← TsModel.f x)) : JsM Bool) = pure true))
  return v.szs == .Inappropriate &&
    v.reason == "the property reaches code outside the model: 'Math.log' is not supported"

-- The off-path direction — a guard that refutes the residual's arm, so
-- every leaf closes and no docstring is read — needs the whole ladder, and
-- is pinned end to end by `tests/fixtures/residual.lean`.

-- The taken arm fails on its own arithmetic while the residual arm is
-- unrefuted: that is a GaveUp about the arithmetic, not an Inappropriate.
@[js_norm, grind]
noncomputable def TsModel.g (x : JsNumber) : JsM JsNumber := do
  if Float.lt x 0 then
    return (← TsModel.f.residual_1 x)
  return x + 1

/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let v ← grindOn (← `(∀ (x : JsNumber), Float.le 0 x = true →
    ((do return Float.le x (← TsModel.g x)) : JsM Bool) = pure true))
  return v.szs == .GaveUp && (v.reason.splitOn "unsolved goal:").length > 1

-- Two sites are never identified, so their difference is not 0 and both
-- constructs reach the verdict, in name order.
/-- 'probe' could not be modeled: unmapped TypeScript construct 'DeclareKeyword' at 1:1 -/
noncomputable opaque TsModel.h.residual_1 : (x : JsNumber) → JsM JsNumber
/-- 'probe' could not be modeled: unmapped TypeScript construct 'DeclareKeyword' at 2:1 -/
noncomputable opaque TsModel.h.residual_2 : (x : JsNumber) → JsM JsNumber

@[js_norm, grind]
noncomputable def TsModel.h (x : JsNumber) : JsM JsNumber := do
  return (← TsModel.h.residual_1 x) - (← TsModel.h.residual_2 x)

/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let v ← grindOn (← `(ballIco 0 5 fun x =>
    ((do return Float.beq 0 (← TsModel.h (Float.ofInt x))) : JsM Bool) = pure true))
  return v.szs == .Inappropriate &&
    v.reason == "the property reaches code outside the model: " ++
      "'probe' could not be modeled: unmapped TypeScript construct 'DeclareKeyword' at 1:1; " ++
      "'probe' could not be modeled: unmapped TypeScript construct 'DeclareKeyword' at 2:1"

-- The site scan reads this artifact's own opaques and nothing else: a
-- library definition is not a residual however the goal mentions it.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let p ← Elab.Term.elabTerm (← `(Float.le 0 floatInf = true)) (some (mkSort .zero))
  return (← residualSites p).isEmpty
