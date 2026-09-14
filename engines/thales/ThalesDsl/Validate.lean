import Lean
import Tarski.Project
import ThalesDsl.Prove

/-! `#thales_validate`: the correspondence command.

A `#thales_prove` verdict is a statement about a declaration's *model* —
the shallow Lean `def` the emitter wrote from the TypeScript. This command
proves that the model *is* the declaration: that running tarski's
evaluator on the declaration's own AST, projected into the model's terms,
equals the model, on every typed input (the design record's D1),

    ∀ args, Tarski.project read
        (Tarski.runScript (TsModel.f.ast ++ [.exprStmt (.call (.ident "f") args)]))
      = some (Tarski.Outcome.ofModel (TsModel.f args))

**Every path prints one `thales-model:` line and no path raises** (D6). A
stuck proof, a spent budget, an obligation that will not even elaborate:
each is a line saying `unvalidated` with a reason, never an elaboration
error. An error here would fail the artifact, and every verdict in the
file with it — and a correspondence that is not established changes no
verdict (D7), since `simp` can only get stuck, never refute.

**The four reasons D7 names**, plus the three this command needs and D7
did not anticipate, are the `*Reason` functions below and the emitter's
bare form (`ThalesEmit/Validate.lean`): every model line, obligation or
not, comes through this one channel so the CLI has one source to join.

**The recipe.** `simp` with the evaluator's own partial-evaluation set
(`tarski_eval`), the model's normalization set (`js_norm`), and the
artifact's own defs unfolded — `TsModel.f.ast` and `TsModel.f` are
file-local, so "no module index and a definition" picks exactly them.
Then a second plain `simp`, which clears the `decide` residue a
boolean-returning declaration leaves. Then, bounded by fuel rather than
by a budget, a case split on the `Bool` an emitted comparison denotes:
`Float.lt`, `Float.le`, `Float.beq`, `JsVal.strictEq` all reach the goal
as `c = true`, on the evaluator's side under an `if` and on the model's
under a `decide`, and splitting the one splits the other.
`Test/Tarski/ProjectSimpTest.lean`'s header says why this is not `split`:
`split` picks the projection's own outer `match`, which is not the branch
in question. -/

register_option thales.validateHeartbeats : Nat := {
  defValue := 2000000
  descr := "per-declaration heartbeat budget for #thales_validate, in the maxHeartbeats unit, the kernel's check of the correspondence theorem included; exhaustion reports the model unvalidated with the budget reason rather than failing the artifact. 0 is clamped to 1, as thales.heartbeats is"
}

namespace ThalesDsl

open Lean Elab Command Meta
open Js

/-- What the closer did with the obligation. `simp` cannot refute, so
there is no third answer: either the proof term is here, or the goal it
stopped on is. -/
inductive ValidateOutcome where
  | proved (proof : Expr)
  /-- The goal the closer stopped on, kept as its metavariable rather than
  as a bare type: a residual is read in its own local context, where the
  declaration's binders and the case split's hypotheses have names. -/
  | stuck (goal : MVarId)

/-- What `simp [tarski_eval, js_norm, *, <the artifact's own defs>]` means
in meta code.

The theorems are the default set, the evaluator's, the model
normalization set's, every hypothesis in scope (the case split's, and a
binder's own), and every constant of the goal that this file defines —
`TsModel.f.ast` and `TsModel.f`, which carry no attribute of their own
and would otherwise stand. The simprocs are the default ones, the
symbolic evaluator's, and the two sets' own — `tarski_eval`'s four
guarded heap steps are simprocs, so a set that dropped them would not
reduce a prototype walk at all. -/
def validateSimpContext (g : MVarId) : MetaM (Simp.Context × Simp.SimprocsArray) :=
  g.withContext do
    let env ← getEnv
    let some evalExt ← Meta.getSimpExtension? `tarski_eval
      | throwError "the evaluator's `tarski_eval` simp set is not registered"
    let some normExt ← Meta.getSimpExtension? `js_norm
      | throwError "the prover's `js_norm` simp set is not registered"
    let mut locals : Meta.SimpTheorems := {}
    for c in (← instantiateMVars (← g.getType)).getUsedConstants do
      if env.getModuleIdxFor? c |>.isNone then
        if let some (.defnInfo _) := env.find? c then
          locals ← locals.addDeclToUnfold c
    for h in ← getLocalHyps do
      if ← Meta.isProp (← inferType h) then
        locals ← locals.add (.fvar h.fvarId!) #[] h
    let ctx ← Meta.Simp.mkContext (config := {})
      (simpTheorems :=
        #[← getSimpTheorems, ← evalExt.getTheorems, ← normExt.getTheorems, locals])
      (congrTheorems := ← Meta.getSimpCongrTheorems)
    let mut procs : Simp.SimprocsArray :=
      #[← Meta.Simp.getSimprocs, ← Meta.Simp.getSEvalSimprocs]
    for a in [`tarski_eval, `js_norm] do
      if let some ext ← Meta.Simp.getSimprocExtension? a then
        procs := procs.push (← ext.getSimprocs)
    return (ctx, procs)

/-- One `simp` pass. `none` is a closed goal; a pass that makes no
progress — which `simpGoal` reports by failing — leaves the goal
untouched for the next step rather than ending the attempt. -/
def simpPass (g : MVarId) (ctx : Simp.Context) (procs : Simp.SimprocsArray) :
    MetaM (Option MVarId) := do
  let r ←
    try Meta.simpGoal g ctx (simprocs := procs)
    catch _ => pure (some (#[], g), {})
  match r.1 with
  | none => return none
  | some (_, g) => return some g

/-- Whether a `Bool`-valued expression is one the split can learn
anything from: not a literal, and not under a binder the goal has not
introduced. -/
private def splittableBool (c : Expr) : Bool :=
  !c.hasLooseBVars && !c.isConstOf ``Bool.true && !c.isConstOf ``Bool.false

/-- The first `c = true` in the goal whose `c` is worth splitting on. That
is the shape every emitted comparison takes: `Float.lt`, `Float.le`,
`Float.beq` and `JsVal.strictEq` are `Bool`-valued, and the coercion into
a `Prop` — the evaluator's `if` condition and the model's `decide` alike
— spells it this way. -/
def boolAtom? (e : Expr) : Option Expr :=
  match e.find? fun s =>
    s.isAppOfArity ``Eq 3 &&
      (s.getArg! 0).isConstOf ``Bool &&
      (s.getArg! 2).isConstOf ``Bool.true &&
      splittableBool (s.getArg! 1) with
  | some s => some (s.getArg! 1)
  | none => none

/-- Split the goal on a `Bool` atom, leaving `c = true` in one branch and
`c = false` in the other. `byCases` leaves the negative branch holding
`¬(c = true)`, which rewrites the proposition but not `c` itself;
`Bool.not_eq_true` is the same fact written as the equation `simp` can
rewrite a `match` scrutinee by. -/
def boolByCases (g : MVarId) (c : Expr) : MetaM (MVarId × MVarId) := do
  let (pos, neg) ← g.byCases (← mkEq c (mkConst ``Bool.true)) `hb
  let negId ← neg.mvarId.withContext do
    let asEq := mkApp (mkConst ``Bool.not_eq_true) c
    let r ← neg.mvarId.replace neg.fvarId (← mkEqMP asEq (mkFVar neg.fvarId))
      (← mkEq c (mkConst ``Bool.false))
    pure r.mvarId
  return (pos.mvarId, negId)

/-- The closer, on one goal. Two `simp` passes — the evaluator's set, then
the default one for the `decide` residue a boolean-returning declaration
leaves — and then a case split on the first `Bool` atom left standing,
recursively.

`fuel` bounds the *shape* of the search, not its cost: the budget is the
heartbeat window the command runs under, and a declaration with more
guards than this many is not one more heartbeats would settle. The goal
reported is the one the recursion first stopped on, which is the branch a
reader has to look at. -/
partial def closeValidate (fuel : Nat) (g : MVarId) : MetaM (Option MVarId) := do
  let (ctx, procs) ← validateSimpContext g
  let some g ← simpPass g ctx procs | return none
  let some g ← simpPass g (← Meta.Simp.mkContext (config := {})
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← Meta.getSimpCongrTheorems))
      #[← Meta.Simp.getSimprocs] | return none
  if fuel == 0 then return some g
  let some c := boolAtom? (← instantiateMVars (← g.getType)) | return some g
  let (pos, neg) ← boolByCases g c
  match ← closeValidate (fuel - 1) pos with
  | some stuck => return some stuck
  | none => closeValidate (fuel - 1) neg

/-- The obligation, attempted. The binders are introduced first, under the
names the obligation gave them — the quantification is over the declared
parameter types, the closer works on the body, and a residual reads as
the source's parameters rather than as daggered placeholders. A proof
that still carries a metavariable is not a proof, so it is reported stuck
rather than handed to `addDecl`. -/
def validateGoal (p : Expr) : Term.TermElabM ValidateOutcome := do
  let mvar ← Meta.mkFreshExprMVar p
  let (_, g) ← mvar.mvarId!.introNP (Meta.getIntrosSize (← instantiateMVars p))
  match ← closeValidate 32 g with
  | some stuck => return .stuck stuck
  | none =>
    let proof ← instantiateMVars mvar
    if proof.hasExprMVar then return .stuck g
    return .proved proof

/-- A validated correspondence is added to the environment under its own
namespace, so the artifact's environment tells it from a proved property
(`TsProof`); the kernel checks it here, as it does a verdict's theorem. -/
def addValidatedTheorem (identity : Identity) (p proof : Expr) :
    Term.TermElabM Name := do
  let thmName := freshTheoremName (← getEnv) identity `TsValidated
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := thmName, levelParams := [], type := p, value := proof })
  return thmName

/-- D7's stuck reason: `simp` cannot refute, so this says the proof did
not get there, never that the model is wrong. -/
def stuckReason (fn : String) : String :=
  s!"the run of '{fn}' did not reduce to its model"

/-- D7's budget reason, naming the option a caller would raise. -/
def budgetReason (budget : Nat) : String :=
  s!"budget: the attempt exceeded thales.validateHeartbeats = {budget}"

/-- An obligation the emitter wrote and Lean will not read. That is an
emitter bug, reported as an unvalidated model rather than as an error:
the artifact's verdicts are not this declaration's to lose. -/
def elabReason (fn msg : String) : String :=
  s!"the obligation of '{fn}' did not elaborate: {msg}"

syntax "#thales_validate " str ppSpace str " := " term : command

elab_rules : command
  | `(#thales_validate $file:str $fn:str := $p:term) => do
    let f := file.getString
    let name := fn.getString
    let budget := max (thales.validateHeartbeats.get (← getOptions)) 1
    let line : ModelLine ←
      try
        liftTermElabM <|
          tryCatchRuntimeEx
            (withAtLeastMaxRecDepth 8000 do
              -- Reading the obligation is not part of the proof budget: an
              -- artifact run at one heartbeat must still elaborate its
              -- statements, or every declaration would report the budget
              -- with its binders half-elaborated. The statement is a term
              -- the emitter wrote, contained by the ambient budget and by
              -- the artifact's own timeout; the budget below is what the
              -- closer and the kernel spend.
              let goal ← Term.withoutErrToSorry do
                let e ← Term.elabTerm p (some (mkSort .zero))
                Term.synthesizeSyntheticMVarsNoPostponing
                instantiateMVars e
              withHeartbeats budget do
                match ← validateGoal goal with
                | .proved proof =>
                  let _ ← addValidatedTheorem ⟨f, name, "model"⟩ goal proof
                  return ModelLine.validated f name
                | .stuck stuck =>
                  -- The diagnostics stream, not the envelope (D6), and
                  -- `logInfo` rather than `logError`: an error would give
                  -- the artifact a nonzero exit and cost every verdict in
                  -- it.
                  stuck.withContext do
                    logInfo m!"unvalidated '{name}': {← instantiateMVars (← stuck.getType)}"
                  return ModelLine.unvalidated f name (stuckReason name))
            fun ex => do
              if ex.isMaxHeartbeat || (← isKernelTimeout ex) then
                return ModelLine.unvalidated f name (budgetReason budget)
              let msg ← ex.toMessageData.toString
              logInfo m!"unvalidated '{name}': {msg}"
              return ModelLine.unvalidated f name (elabReason name msg)
      catch ex =>
        pure (ModelLine.unvalidated f name
          (elabReason name (← ex.toMessageData.toString)))
    line.emit

/-- The bare form: the emitter's report for a declaration that gets no
obligation at all — a tainted one, one with no closed script, one the
decoder refused, one with a parameter this slice does not quantify. The
line is the same line, so the CLI has one channel and one join. -/
syntax "#thales_validate " str ppSpace str " unvalidated " str : command

elab_rules : command
  | `(#thales_validate $file:str $fn:str unvalidated $reason:str) =>
    ModelLine.emit
      (ModelLine.unvalidated file.getString fn.getString reason.getString)

end ThalesDsl
