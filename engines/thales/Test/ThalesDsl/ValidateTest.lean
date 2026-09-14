import ThalesDsl

open Js ThalesDsl Lean

/-! The correspondence closer, on the four shapes it has to answer for.

These are `validateGoal` directly rather than `#thales_validate`: the
command's own output — one `thales-model:` line per command, whatever
happens — is pinned by `scripts/check-verdict-channel.js` over
`tests/fixtures/validate.lean`, as `ResidualTest`'s header says of the
verdict channel. What is here is the tactic underneath it.

A whole-program `simp` partially evaluates the realm, so these need more
room than a closed goal does, exactly as `Test/Tarski/ProjectSimpTest.lean`
does — and rather more wall clock: the free-function obligation below
takes about half a minute on a laptop, which is the measurement the
default `thales.validateHeartbeats` is set from. -/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-- `function add(a, b) { return a + b; }` -/
private def addAst : Tarski.Program :=
  [.funcDecl "add" ["a", "b"] [.returnStmt (some (.binary .add (.ident "a") (.ident "b")))]]

private def addModel (a b : JsNumber) : JsM JsNumber := .ok (a + b)

/-- `function isSmall(n) { return n < 5; }` -/
private def isSmallAst : Tarski.Program :=
  [.funcDecl "isSmall" ["n"] [.returnStmt (some (.binary .lt (.ident "n") (.numLit 5.0)))]]

private def isSmallModel (n : JsNumber) : JsM Bool := .ok (Float.lt n 5.0)

/-- A model that adds one where the program adds two: `simp` cannot refute
it, so the closer gets stuck rather than answering. -/
private def wrongModel (a : JsNumber) : JsM JsNumber := .ok (a + 1.0)

private def addGoal : TSyntax `term :=
  Unhygienic.run `(∀ (a b : JsNumber),
    Tarski.project Tarski.readNumber
        (Tarski.runScript (addAst ++ [.exprStmt (.call (.ident "add") [.numLit a, .numLit b])]))
      = some (Tarski.Outcome.ofModel (addModel a b)))

private def wrongGoal : TSyntax `term :=
  Unhygienic.run `(∀ (a : JsNumber),
    Tarski.project Tarski.readNumber
        (Tarski.runScript (addAst ++ [.exprStmt (.call (.ident "add") [.numLit a, .numLit a])]))
      = some (Tarski.Outcome.ofModel (wrongModel a)))

private def isSmallGoal : TSyntax `term :=
  Unhygienic.run `(∀ (n : JsNumber),
    Tarski.project Tarski.readBool
        (Tarski.runScript (isSmallAst ++ [.exprStmt (.call (.ident "isSmall") [.numLit n])]))
      = some (Tarski.Outcome.ofModel (isSmallModel n)))

private def elabProp (t : TSyntax `term) : Elab.Term.TermElabM Expr := do
  let e ← Elab.Term.elabTerm t (some (mkSort .zero))
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

-- A free function over two number parameters: proved, and the proof term
-- is complete — a proof still carrying a metavariable is not one, and
-- `addDecl` would reject it late instead of the command reporting it.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  match ← validateGoal (← elabProp addGoal) with
  | .proved proof => return !proof.hasExprMVar
  | .stuck _ => return false

-- A wrong model: stuck, never refuted. `simp` has no way to say "false",
-- which is the whole reason an unvalidated model changes no verdict.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  match ← validateGoal (← elabProp wrongGoal) with
  | .proved _ => return false
  | .stuck _ => return true

-- A boolean-returning function: the comparison survives the first pass as
-- a `Bool` under `= true`, and the case split closes both branches.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  match ← validateGoal (← elabProp isSmallGoal) with
  | .proved _ => return true
  | .stuck _ => return false

-- The atom the split looks for: a `Bool` under `= true` that is neither a
-- literal nor still under a binder. The binder case is why `validateGoal`
-- introduces before it closes — splitting on a term with a loose bound
-- variable in it is not a case split on anything.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let atom ← elabProp (Unhygienic.run `((Float.lt 1.0 5.0 = true) = True))
  let literal ← elabProp (Unhygienic.run `((true = true) = True))
  let bound ← elabProp (Unhygienic.run `(∀ (n : JsNumber), (Float.lt n 5.0 = true) = True))
  return (boolAtom? atom).isSome && (boolAtom? literal).isNone
    && (boolAtom? bound).isNone

-- Budget exhaustion is the exception path, not a return value: the
-- command's own handler is what turns it into the budget reason, so it
-- has to reach the handler.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let p ← elabProp addGoal
  tryCatchRuntimeEx
    (do let _ ← withHeartbeats 1 (validateGoal p); return false)
    (fun ex => return ex.isMaxHeartbeat)

-- A validated correspondence is named apart from a proved property, so an
-- artifact's environment tells the two kinds of theorem apart.
/-- info: true -/
#guard_msgs in
#eval show Elab.Term.TermElabM Bool from do
  let n := freshTheoremName (← getEnv) ⟨"f.ts", "fn", "model"⟩ `TsValidated
  return n.toString.startsWith "TsValidated.thm_"
