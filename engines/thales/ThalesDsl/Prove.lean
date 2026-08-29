import Lean
import Js.Number.Basic
import ThalesDsl.Verdict

register_option thales.heartbeats : Nat := {
  defValue := 200000
  descr := "per-annotation heartbeat budget for #thales_prove, in the maxHeartbeats unit; an attempt that exceeds it reports a Timeout verdict. 0 is clamped to 1: the underlying limit reads 0 as unlimited, which would leave the attempt uncontained"
}

register_option thales.maxEvaluatedElements : Nat := {
  defValue := 10000000
  descr := "the largest bounded domain #thales_prove will settle by evaluating the property at every element. Evaluation runs compiled, so the heartbeat budget cannot interrupt it; this cap is what keeps a wide domain from spending an unbounded amount of wall clock. A larger domain falls through to symbolic reasoning instead"
}

namespace ThalesDsl

open Lean Elab Command
open Js

/-- Successful proofs are added to the environment so the kernel — not just
the elaborator — has checked them. -/
def freshTheoremName (env : Environment) (identity : Identity) : Name := Id.run do
  let base := `TsProof ++
    Name.mkSimple s!"thm_{hash s!"{identity.file}#{identity.function}#{identity.property}"}"
  let mut name := base
  let mut i : Nat := 1
  while env.contains name do
    i := i + 1
    name := base.appendAfter s!"_{i}"
  return name

/-- Reads back a fully reduced `Int` literal: a constructor applied to a
raw `Nat` literal. -/
def readInt (e : Expr) : Option Int :=
  if e.isAppOfArity ``Int.ofNat 1 then (e.getArg! 0).rawNatLit?.map Int.ofNat
  else if e.isAppOfArity ``Int.negSucc 1 then (e.getArg! 0).rawNatLit?.map Int.negSucc
  else none

/-- Reads back a fully reduced `List Int` literal. -/
partial def readIntList (e : Expr) : Option (List Int) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then do
    let head ← readInt (e.getArg! 1)
    let tail ← readIntList (e.getArg! 2)
    return head :: tail
  else none

/-- Evaluates the witness-search term and pairs the values with the binder
names. Wholly best-effort: every failure degrades to `none` instead of
escaping, a spent resource limit included. The sole caller runs this after
falsity is already established, and an established verdict must not be lost
to the cost of illustrating it. -/
def extractWitness (names : List String) (searchStx : TSyntax `term) :
    Term.TermElabM (Option (Array (String × Int))) :=
  tryCatchRuntimeEx
    (try
      let s ← Term.withoutErrToSorry do
        let s ← Term.elabTerm (← `(($searchStx : Option (List Int)))) none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars s
      let r ← Meta.reduce s (explicitOnly := false) (skipTypes := true) (skipProofs := true)
      if r.isAppOfArity ``Option.some 2 then
        if let some vals := readIntList (r.getArg! 1) then
          if vals.length == names.length then
            return some (names.zip vals).toArray
      return none
    catch _ => return none)
    (fun _ => return none)

/-- After the kernel rejects a decide proof, reduce the `Decidable` instance
to tell a false property from one the kernel could not evaluate. The instance
is re-synthesized from the proposition so nothing depends on the proof term's
internal shape; the reduction is best-effort — failures degrade to `none`,
except a blown heartbeat budget, which propagates as the annotation's
Timeout: falsity was not established, so the rung really did starve.
Established falsity is terminal, and nothing after it can take it back: with
binders and a searched-out witness it ships as `CounterSatisfiable`,
otherwise — no binders, or a witness search that came back empty — as a
false-on-domain `GaveUp`. `none` means the instance stayed stuck — the
generic stage still gets its turn. -/
def diagnoseDecideFailure (identity : Identity) (p : Expr)
    (names : List String) (searchStx : TSyntax `term) :
    Term.TermElabM (Option Verdict) := do
  let falseOnDomain : Verdict := ⟨identity, .GaveUp,
    "the property is false on its bounded domain", none, none⟩
  tryCatchRuntimeEx
    (do
      let inst ← Meta.synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← Meta.withAtLeastTransparency .default <| Meta.whnf inst
      if r.isAppOf ``Decidable.isFalse then
        if names.isEmpty then return some falseOnDomain
        if let some cex ← extractWitness names searchStx then
          return some ⟨identity, .CounterSatisfiable,
            "the property is false on its bounded domain", some cex, none⟩
        return some falseOnDomain
      return none)
    (fun ex => if ex.isMaxHeartbeat then throw ex else return none)

/-- Runs `x` under a fresh heartbeat budget (in the `maxHeartbeats` option's
unit). The enforced limit is cached in the Core context at context creation,
so the field must be set directly; the option is kept in sync for anything
that reads it. -/
def withHeartbeats {α : Type} (budget : Nat) (x : Term.TermElabM α) : Term.TermElabM α :=
  controlAt CoreM fun runInBase => do
    let start ← IO.getNumHeartbeats
    withReader (fun ctx => { ctx with
      initHeartbeats := start
      maxHeartbeats := budget * 1000
      options := maxHeartbeats.set ctx.options budget }) (runInBase x)

/-- The kernel reports its own budget exhaustion as a plain error, not a
runtime exception, so it needs classifying by message. -/
def isKernelTimeout (ex : Exception) : CoreM Bool := do
  match ex with
  | .error _ msg =>
    return ((← msg.toString).splitOn "(kernel) deterministic timeout").length > 1
  | _ => return false

/-- Adds a proof to the environment with async elaboration off (as
`decide +kernel` does), so the kernel checks it here: a bad proof is a
catchable failure, not a late artifact failure. The name is fresh per call —
a failed `addDecl` can leave its name claimed in the environment, so a later
rung must never reuse an earlier rung's. -/
def addTheoremSync (identity : Identity) (p proof : Expr) : Term.TermElabM Name := do
  let thmName := freshTheoremName (← getEnv) identity
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := thmName, levelParams := [], type := p, value := proof })
  return thmName

/-- The axioms every Lean proof may use without extending the trusted base. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- A proved annotation's verdict. `method` names the rung's class — never a
tactic, since dischargers change — but the trust level and the reported
axiom list are read off the theorem's actual axioms rather than asserted by
the rung, which could drift from what happened. Any axiom beyond the
standard three means the result rests on more than the kernel; today that
is native evaluation, which trusts the compiler and the host's floating
point unit. -/
def provedVerdict (identity : Identity) (method : String) (thmName : Name) :
    CoreM Verdict := do
  let axioms ← collectAxioms thmName
  let extra := (axioms.filter (!standardAxioms.contains ·)).qsort
    (fun a b => a.toString < b.toString)
  let reason :=
    if extra.isEmpty then
      s!"proved by {method}, kernel-checked as {thmName}"
    else
      s!"proved by {method}, admitted as {thmName}; the result is " ++
      s!"trusted from evaluation rather than checked by the kernel"
  return ⟨identity, .Theorem, reason, none, some extra⟩

/-- Degrades a rung's plain failure to a fall-through, so the rungs after it
still get their turn. Lean's own `catch` already re-raises runtime exceptions
(heartbeats, recursion depth) for `runRung` to classify, but the kernel
reports its budget exhaustion as an ordinary error, and that is starvation
rather than a rung that simply had nothing to say. -/
def orFallThrough {α : Type} (x : Term.TermElabM α) :
    Term.TermElabM (Option α) := do
  try
    return some (← x)
  catch ex =>
    if ← isKernelTimeout ex then throw ex
    return none

def attemptDecide (identity : Identity) (p : Expr)
    (searchStx : TSyntax `term) (names : List String) :
    Term.TermElabM (Option Verdict) := do
  let some proof ← (try some <$> Meta.mkDecideProof p catch _ => pure none)
    -- decide could not even build its proof; the generic stage still gets
    -- its turn.
    | return none
  try
    let thmName ← addTheoremSync identity p proof
    return some (← provedVerdict identity
      "a decision procedure over the bounded domain" thmName)
  catch ex =>
    if ← isKernelTimeout ex then throw ex
    return (← diagnoseDecideFailure identity p names searchStx)

/-- Rung 1b: the same goal, evaluated by the compiler rather than the
kernel. Vanilla Lean has no Float theory, so evaluation over the finite
domain is the only route, and the kernel's is too slow past a few hundred
elements. Falsity is reported directly here, so no instance reduction is
needed to tell a false property from a stuck one. -/
def attemptNativeDecide (identity : Identity) (p : Expr)
    (searchStx : TSyntax `term) (names : List String) :
    Term.TermElabM (Option Verdict) := do
  let falseOnDomain : Verdict := ⟨identity, .GaveUp,
    "the property is false on its bounded domain", none, none⟩
  let some d ← (try some <$> Meta.mkDecide p catch _ => pure none)
    | return none
  -- Codegen and evaluation failures surface as ordinary elaboration errors,
  -- not runtime exceptions, so nothing above would catch them: uncontained,
  -- they escape the whole ladder as the annotation's Error.
  let some result ← orFallThrough (Meta.nativeEqTrue `native_decide d)
    | return none
  match result with
  | .notTrue =>
    -- Established falsity is terminal; only the illustration is optional.
    if names.isEmpty then return some falseOnDomain
    if let some cex ← extractWitness names searchStx then
      return some ⟨identity, .CounterSatisfiable,
        "the property is false on its bounded domain", some cex, none⟩
    return some falseOnDomain
  | .success prf =>
    let inst := d.appArg!
    let proof := mkApp3 (mkConst ``of_decide_eq_true) p inst prf
    let some thmName ← orFallThrough (addTheoremSync identity p proof)
      | return none
    return some (← provedVerdict identity
      "a decision procedure over the bounded domain" thmName)

/-- Rung 2's outcome: a verdict, or the state rung 3 continues from — the
root metavariable still linked to the unsolved residual goal. -/
inductive GenericOutcome where
  | done (v : Verdict)
  | stuck (root : Expr) (goal : MVarId) (residual : Expr)

/-- Pretty-prints a residual goal with `Js` and `ThalesDsl` open, so the
reason's wording never depends on the artifact's own header. -/
def ppResidual (e : Expr) : MetaM Format :=
  withTheReader Core.Context
    (fun ctx => { ctx with openDecls := [.simple `Js [], .simple `ThalesDsl []] })
    (Meta.ppExpr e)

/-- What a rung reports when it has nothing to say about the goal it was
left holding. -/
def residualGaveUp (identity : Identity) (residual : Expr) : MetaM Verdict := do
  return ⟨identity, .GaveUp, s!"unsolved goal: {← ppResidual residual}", none, none⟩

/-- Certifies a closed root metavariable through the kernel; anything off
about the proof (kernel budget exhaustion aside) degrades to the
residual-goal GaveUp rather than escaping. -/
def certifyRoot (identity : Identity) (p root residual : Expr) :
    Term.TermElabM Verdict := do
  let gaveUp ← residualGaveUp identity residual
  let proof ← instantiateMVars root
  if proof.hasExprMVar then return gaveUp
  try
    let thmName ← addTheoremSync identity p proof
    return ← provedVerdict identity "generic proof search" thmName
  catch ex =>
    if ← isKernelTimeout ex then throw ex
    return gaveUp

/-- Rung 2, the generic stage: normalize with the `js_norm` simp set,
then close with omega. Success is kernel-checked like the decide rung; a
closer that fails leaves the residual goal — rolled back to its
pre-closer state — for the next rung. -/
def attemptGeneric (identity : Identity) (p : Expr) :
    Term.TermElabM GenericOutcome := do
  let mvar ← Meta.mkFreshExprMVar p
  let some ext ← Meta.getSimpExtension? `js_norm
    | return .done ⟨identity, .Error,
      "the prover's normalization rules are not registered", none, none⟩
  let ctx ← Meta.Simp.mkContext (config := {})
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← Meta.getSimpCongrTheorems)
  let simped ←
    try Meta.simpGoal mvar.mvarId! ctx (simprocs := #[← Meta.Simp.getSEvalSimprocs])
    catch _ => pure (some (#[], mvar.mvarId!), {})
  match simped.1 with
  | none => return .done (← certifyRoot identity p mvar p)
  | some (_, g) =>
    let residual ← instantiateMVars (← g.getType)
    let s ← saveState
    let closed ←
      try
        match ← g.falseOrByContra with
        | none => pure true
        | some gFalse =>
          gFalse.withContext do
            Tactic.Omega.omega (← getLocalHyps).toList gFalse {}
          pure true
      catch _ =>
        -- The failed closer may have half-assigned the goal; restore so
        -- the next rung sees it untouched.
        restoreState s
        pure false
    if closed then return .done (← certifyRoot identity p mvar residual)
    return .stuck mvar g residual

/-- A hypothesis that names a local as some computation's successful
result: `<computation> = .ok x`. That is the shape a class binder's
constructor-image hypothesis has, and the only one the step below
touches. -/
def ctorImageHyp? (goal : MVarId) : MetaM (Option FVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if let some (_, _, rhs) := decl.type.eq? then
        if rhs.isAppOfArity ``Except.ok 3 && (rhs.getArg! 2).isFVar then
          return some decl.fvarId
    return none

/-- The conditionals an inversion leaves in the goal. A constructor that
computes a field value with one — the shape a `?:` normalization takes —
has it substituted into the goal, where `grind` does not split it either,
so the field would keep its whole `ite` term. Shares the inversion's fuel,
which bounds the fan-out the same way. -/
partial def splitFieldIfs (goal : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  if fuel == 0 then return [goal]
  match ← observing? (Meta.splitTarget? goal) with
  | some (some goals) =>
    return (← goals.mapM (splitFieldIfs · (fuel - 1))).flatten
  | _ => return [goal]

/-- `grind` neither case-splits an `if` sitting inside a hypothesis nor
carries a constructor equation into the goal, so a class binder's
constructor-image hypothesis never reaches the field values the closers
need. Split those hypotheses until each names a constructor, invert them,
and substitute. The fuel bounds the fan-out: a constructor with several
guards would otherwise branch past any budget, and reaching the bound
just leaves the goal for grind to fail on. -/
partial def invertCtorImage (goal : MVarId) (fuel : Nat) (inverted := false) :
    MetaM (List MVarId) := do
  if fuel == 0 then return [goal]
  let some fvarId ← ctorImageHyp? goal
    | if inverted then return ← splitFieldIfs goal fuel else return [goal]
  match ← observing? (Meta.injection goal fvarId) with
  | some .solved => return []
  | some (.subgoal g _ _) => invertCtorImage (← Meta.substVars g) (fuel - 1) true
  | none =>
    match ← Meta.splitIfLocalDecl? goal fvarId with
    | some (g₁, g₂) =>
      return (← invertCtorImage g₁ (fuel - 1) inverted)
        ++ (← invertCtorImage g₂ (fuel - 1) inverted)
    | none => return [goal]

/-- How deep the inversion may branch. Each level either discharges one
constructor-image hypothesis or splits one guard, so this covers a
two-binder formula over a constructor with a handful of guards. -/
def ctorImageFuel : Nat := 12

/-- Drops the hypotheses that cannot bear on the target. Reach spreads:
a hypothesis counts once it mentions a variable the target already
reaches, and then its own variables are reached too — a guard on a
constructor argument is live while the hypothesis naming that
constructor's image is, even before the image has been inverted. What
never gets reached links to nothing the goal asks about, and dropping it
is what lets two goals that differ only in a dead guard recognize each
other. -/
def clearDeadHyps (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut hyps : Array (FVarId × Array FVarId) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← Meta.isProp decl.type do continue
    hyps := hyps.push
      (decl.fvarId, (collectFVars {} (← instantiateMVars decl.type)).fvarIds)
  let mut reached := (collectFVars {} (← instantiateMVars (← goal.getType))).fvarSet
  let mut live : FVarIdSet := {}
  -- Each pass reaches at least one more hypothesis or there is no next one.
  for _ in [0:hyps.size] do
    let mut grew := false
    for (fvarId, vars) in hyps do
      if live.contains fvarId then continue
      -- A hypothesis over no variable at all — a contradiction among them
      -- — is about the goal as much as anything is.
      if vars.isEmpty || vars.any (reached.contains ·) then
        live := live.insert fvarId
        for v in vars do reached := reached.insert v
        grew := true
    unless grew do break
  let mut g := goal
  for (fvarId, _) in hyps do
    unless live.contains fvarId do
      g ← g.tryClear fvarId
  return g

/-- Normalizes a goal and drops what cannot bear on its target: the shape
every leaf is measured and closed in. `none` means normalization closed the
goal outright. -/
def normalizeLeaf (ctx : Meta.Simp.Context) (simprocs : Meta.Simp.SimprocsArray)
    (goal : MVarId) : MetaM (Option MVarId) := do
  -- A goal simp has nothing to say about is the goal itself: the
  -- no-progress failure is not the rung's failure.
  let simped ←
    try
      let r ← Meta.simpGoal goal ctx (simprocs := simprocs)
      pure r.1
    catch _ => pure (some (#[], goal))
  let some (_, g) := simped | return none
  return some (← clearDeadHyps g)

/-- Rung 3: grind on the residual goal rung 2 left. Success certifies
through the root metavariable like every rung; a grind that simply fails
ships the residual-goal GaveUp. Neither resource limit is contained here:
this rung's exhaustion is classified where every other rung's is, so a
spent budget can still report as the annotation's Timeout.

Each leaf is normalized, stripped of what cannot bear on it, and closed
over what survives, and leaves that agree there are merged: a guard on a
field the property never reads leaves no trace in the leaves it doubled,
so they prove once between them. -/
def attemptGrind (identity : Identity) (p root : Expr) (goal : MVarId)
    (residual : Expr) : Term.TermElabM Verdict := do
  let solved := (← orFallThrough do
    let params ← Meta.Grind.mkDefaultParams {}
    -- Normalization is what makes two leaves comparable, not what makes
    -- them provable: without the rule set every leaf simply stands alone.
    let norm? ← do
      let some ext ← Meta.getSimpExtension? `js_norm | pure none
      let ctx ← Meta.Simp.mkContext (config := {})
        (simpTheorems := #[← ext.getTheorems])
        (congrTheorems := ← Meta.getSimpCongrTheorems)
      pure (some (ctx, (#[← Meta.Simp.getSEvalSimprocs] : Meta.Simp.SimprocsArray)))
    let goals ← invertCtorImage (← goal.intros).2 ctorImageFuel
    -- Two leaves that agree once closed over their own contexts are one
    -- sequent: syntactic equality on a closed type is α-equivalence, so
    -- they share a single grind run and a single proof term.
    let mut classes : Std.HashMap Expr (Array MVarId) := {}
    let mut alone : Array MVarId := #[]
    for g in goals do
      match norm? with
      | none => alone := alone.push g
      | some (ctx, simprocs) =>
        let some g ← normalizeLeaf ctx simprocs g | continue
        let g ← g.revertAll
        let ty ← instantiateMVars (← g.getType)
        classes := classes.insert ty ((classes.getD ty #[]).push g)
    let mut ok := true
    for g in alone do
      if (← Meta.Grind.main g params).hasFailed then
        ok := false
        break
    if ok then
      for (_, members) in classes do
        let rep := members[0]!
        if (← Meta.Grind.main rep params).hasFailed then
          ok := false
          break
        let proof ← instantiateMVars (Expr.mvar rep)
        for dup in members[1:] do
          dup.assign proof
    pure ok).getD false
  if solved then return ← certifyRoot identity p root residual
  return ← residualGaveUp identity residual

def timeoutVerdict (identity : Identity) (budget : Nat) : Verdict :=
  ⟨identity, .Timeout,
    s!"the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = {budget})", none, none⟩

/-- The ladder's exit. A starved rung might have closed the goal given
budget, so exhaustion plus a residual goal is budget exhaustion rather than
a dead end. -/
def ladderVerdict (identity : Identity) (budget : Nat) (starved : Bool)
    (v : Verdict) : Verdict :=
  if starved && v.szs == .GaveUp then timeoutVerdict identity budget else v

/-- Runs one rung, turning either resource limit into a fall-through to the
next. Budget exhaustion — heartbeats, or the kernel's own timeout — reports
the rung starved, since a bigger budget might have closed the goal; a blown
recursion limit does not, so it falls through as a plain rung failure. -/
def runRung {α : Type} (x : Term.TermElabM α) :
    Term.TermElabM (Option α × Bool) :=
  tryCatchRuntimeEx (return (some (← x), false))
    (fun ex => do
      if ex.isMaxHeartbeat || (← isKernelTimeout ex) then return (none, true)
      if ex.isMaxRecDepth then return (none, false)
      throw ex)

def attemptLadder (identity : Identity) (propStx : TSyntax `term)
    (searchStx : TSyntax `term) (names : List String) (allBounded : Bool)
    (domainSize : Nat) (budget : Nat) (evalCap : Nat) :
    Term.TermElabM Verdict := do
  -- A plain catch would let the recursion limit through to the caller,
  -- which would read this phase's failure as proof search's; budget
  -- exhaustion still propagates, as the annotation's Timeout.
  let elaborated : Except Verdict Expr ←
    tryCatchRuntimeEx
      (do
        let p ← withHeartbeats budget <| Term.withoutErrToSorry do
          let p ← Term.elabTerm propStx (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars p
        return .ok p)
      (fun ex => do
        if ex.isMaxHeartbeat || (← isKernelTimeout ex) then throw ex
        return .error ⟨identity, .Error,
          s!"property elaboration failed: {← ex.toMessageData.toString}", none, none⟩)
  let p ← match elaborated with
    | .ok p => pure p
    | .error v => return v
  -- Each rung runs under its own fresh window: the kernel overshoots a
  -- shared window by a large factor before its own counter fires, which
  -- would let an early rung's blowout starve the ones after it. Four rungs
  -- now. A bounded run splits the budget evenly across the two decide tiers
  -- and the two symbolic ones; an unbounded run has no decide tier to fund,
  -- and the two symbolic rungs are not the same kind of work — the generic
  -- rung normalizes, which costs what the goal's size costs, while the grind
  -- rung searches, which is where a wide goal spends — so the search takes
  -- what the decide tiers would have had. Every share floors at 1, since a
  -- zero budget reads as unlimited.
  let quarter := max (budget / 4) 1
  let half := max (budget / 2) 1
  let decideShare := quarter
  let genericShare := quarter
  let grindShare := if allBounded then quarter else half + quarter
  let mut starved := false
  if allBounded then
    let (outcome, rungStarved) ←
      runRung (withHeartbeats decideShare (attemptDecide identity p searchStx names))
    if let some (some v) := outcome then return v
    -- Kernel starvation is no longer the annotation's Timeout: the
    -- evaluation tier gets the same goal, and it is orders of magnitude
    -- faster. It runs compiled, though, so no budget can interrupt it once
    -- started; a domain past the cap is left to the symbolic rungs, and the
    -- starved kernel tier still reports the attempt as budget-bound.
    let mut nStarved := false
    if domainSize ≤ evalCap then
      let (nOutcome, s) ←
        runRung (withHeartbeats decideShare (attemptNativeDecide identity p searchStx names))
      if let some (some v) := nOutcome then return v
      nStarved := s
    if rungStarved || nStarved then starved := true
  let (outcome, rungStarved) ←
    runRung (withHeartbeats genericShare (attemptGeneric identity p))
  if rungStarved then starved := true
  -- Rung 3 takes the goal rung 2 was left holding, or — when rung 2 blew a
  -- limit without leaving a residual — starts over from the original
  -- proposition. One call site either way, so the rung is classified once.
  let (root, goal, residual) ← match outcome with
    | some (.done v) => return ladderVerdict identity budget starved v
    | some (.stuck root goal residual) => pure (root, goal, residual)
    | none => do
      let root ← Meta.mkFreshExprMVar p
      pure (root, root.mvarId!, p)
  let (grindOutcome, grindStarved) ←
    runRung (withHeartbeats grindShare (attemptGrind identity p root goal residual))
  if grindStarved then starved := true
  let v ← match grindOutcome with
    | some v => pure v
    | none => residualGaveUp identity residual
  return ladderVerdict identity budget starved v

end ThalesDsl
