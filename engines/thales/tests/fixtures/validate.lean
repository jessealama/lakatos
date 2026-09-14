import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- The model channel, end to end: one `thales-model:` line per
-- `#thales_validate`, whatever happens to the obligation, and the
-- `#thales_prove` after each one still reports its own verdict. The
-- obligations here are written by hand in the shape `thales-emit`
-- renders, so this file pins the command's own behaviour rather than the
-- emitter's choice of what to state.

-- `export function add(a: number, b: number): number { return a + b; }`,
-- the tracer fixture's AST and model verbatim. At the real budget: the
-- whole realm is partially evaluated and the correspondence theorem is
-- kernel-checked.
def TsModel.add.ast : Tarski.Program :=
  [.funcDecl "add" ["a", "b"] [.returnStmt (some (.binary .add (.ident "a") (.ident "b")))]]

@[js_norm, grind]
def TsModel.add (a b : JsNumber) : JsM JsNumber := do
  return a + b

#thales_validate "engines/thales/tests/fixtures/tracer.ts" "add" :=
  ∀ (a b : JsNumber),
    Tarski.project Tarski.readNumber
        (Tarski.runScript
          (TsModel.add.ast ++ [.exprStmt (.call (.ident "add") [.numLit a, .numLit b])]))
      = some (Tarski.Outcome.ofModel (TsModel.add a b))

-- A deliberately wrong model: `function wrong(a) { return a + 2; }` against
-- a model that adds one. `simp` cannot refute, so the report is that the
-- run did not reduce to the model, the residual goes to the diagnostics
-- stream, and the verdict below is untouched by it (D7).
def TsModel.wrong.ast : Tarski.Program :=
  [.funcDecl "wrong" ["a"] [.returnStmt (some (.binary .add (.ident "a") (.numLit 2.0)))]]

@[js_norm, grind]
def TsModel.wrong (a : JsNumber) : JsM JsNumber := do
  return a + 1.0

#thales_validate "validate.ts" "wrong" :=
  ∀ (a : JsNumber),
    Tarski.project Tarski.readNumber
        (Tarski.runScript
          (TsModel.wrong.ast ++ [.exprStmt (.call (.ident "wrong") [.numLit a])]))
      = some (Tarski.Outcome.ofModel (TsModel.wrong a))

#thales_prove "validate.ts" "wrong" "refl" :=
  ballIco 0 3 fun a => TsModel.wrong (Float.ofInt a) = TsModel.wrong (Float.ofInt a)

-- The same obligation at one heartbeat: budget exhaustion is a model line
-- with the budget reason, never an elaboration error.
set_option thales.validateHeartbeats 1 in
#thales_validate "engines/thales/tests/fixtures/tracer.ts" "add" :=
  ∀ (a b : JsNumber),
    Tarski.project Tarski.readNumber
        (Tarski.runScript
          (TsModel.add.ast ++ [.exprStmt (.call (.ident "add") [.numLit a, .numLit b])]))
      = some (Tarski.Outcome.ofModel (TsModel.add a b))

-- The bare form: the emitter's report for a declaration that gets no
-- obligation at all. Here a tainted one, carrying its residual's construct.
#thales_validate "validate.ts" "pow" unvalidated "'**' is not supported"

-- A boolean-returning declaration: `function isSmall(n) { return n < 5; }`.
-- The comparison reaches the goal as a `Bool` under `= true` on both
-- sides, which is what the closer's case split is for.
def TsModel.isSmall.ast : Tarski.Program :=
  [.funcDecl "isSmall" ["n"] [.returnStmt (some (.binary .lt (.ident "n") (.numLit 5.0)))]]

@[js_norm, grind]
def TsModel.isSmall (n : JsNumber) : JsM Bool := do
  return Float.lt n 5.0

#thales_validate "validate.ts" "isSmall" :=
  ∀ (n : JsNumber),
    Tarski.project Tarski.readBool
        (Tarski.runScript
          (TsModel.isSmall.ast ++ [.exprStmt (.call (.ident "isSmall") [.numLit n])]))
      = some (Tarski.Outcome.ofModel (TsModel.isSmall n))

-- A module constant: `const K = 1000 * 60;`. Its model is a `JsNumber`,
-- not a `JsM`, so the obligation compares against `Outcome.value` rather
-- than against `Outcome.ofModel`.
def TsModel.K.ast : Tarski.Program :=
  [.varDecl .const [{ name := "K", init := some (.binary .mul (.numLit 1000.0) (.numLit 60.0)) }]]

@[js_norm, grind]
def TsModel.K : JsNumber := 1000.0 * 60.0

#thales_validate "validate.ts" "K" :=
  Tarski.project Tarski.readNumber
      (Tarski.runScript (TsModel.K.ast ++ [.exprStmt (.ident "K")]))
    = some (Tarski.Outcome.value TsModel.K)

-- An obligation that will not elaborate. That is an emitter bug, and it is
-- still only this declaration's model that is lost: the file goes on and
-- the command after it reports its own verdict.
#thales_validate "validate.ts" "bad" := Nat.succ "x"

#thales_prove "validate.ts" "bad" "stub"
