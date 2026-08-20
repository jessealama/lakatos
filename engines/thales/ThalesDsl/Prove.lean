import Lean
import ThalesDsl.Verdict
import ThalesDsl.Model

register_option thales.heartbeats : Nat := {
  defValue := 200000
  descr := "per-annotation heartbeat budget for #thales_prove, in the maxHeartbeats unit; an attempt that exceeds it reports a Timeout verdict"
}

namespace ThalesDsl

open Lean Elab Command

/-- One parsed ∀-binder: its variable, plus the range when bounded. -/
inductive BinderShape where
  | ranged (x : String) (lo hi : TSyntax ``tsIntLit)
  | unboundedInt (x : String)
  | unboundedNat (x : String)

def BinderShape.name : BinderShape → String
  | .ranged x .. | .unboundedInt x | .unboundedNat x => x

def BinderShape.isRanged : BinderShape → Bool
  | .ranged .. => true
  | _ => false

/-- What elabProp builds from a ts_prop. `allBounded` gates the decide
rung: without it no Decidable instance exists, and `search` is a stub —
witness search never runs on unbounded domains. -/
structure ElabProp where
  prop : TSyntax `term
  search : TSyntax `term
  names : List String
  allBounded : Bool

/-- Transcribes a `ts_prop` into a Lean `Prop` term — bounded binders become
nested `ballIco`, unbounded int/nat binders plain `∀`s (nat carries its
nonnegativity hypothesis), `≡` equations compare `TsM Int` results, boolean
islands must evaluate to `pure true` — plus a parallel witness-search term
of type `Option (List Int)` (one `findCexIco` per binder, a decidable test
at the leaf) and the binder names in binder order. -/
partial def elabProp (vars : List String) :
    TSyntax `ts_prop → CommandElabM ElabProp
  | `(ts_prop| ts.eq($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .int l
    let rt ← evalExpr vars .int r
    let prop ← `(($lt : TsM Int) = $rt)
    let search ← `(if ($lt : TsM Int) = $rt then (none : Option (List Int)) else some [])
    return ⟨prop, search, [], true⟩
  | `(ts_prop| ts.istrue($e:ts_expr)) => do
    let t ← evalExpr vars .bool e
    let prop ← `(($t : TsM Bool) = pure true)
    let search ← `(if ($t : TsM Bool) = pure true then (none : Option (List Int)) else some [])
    return ⟨prop, search, [], true⟩
  | `(ts_prop| ts.forall($binders:ts_binder,*) {$body:ts_prop}) => do
    let bs ← binders.getElems.mapM fun b => match b with
      | `(ts_binder| ts.binder[$x:str](ts.int, ts.range($lo:tsIntLit, $hi:tsIntLit))) =>
        pure (BinderShape.ranged x.getString lo hi)
      | `(ts_binder| ts.binder[$x:str](ts.int)) =>
        pure (BinderShape.unboundedInt x.getString)
      | `(ts_binder| ts.binder[$x:str](ts.nat)) =>
        pure (BinderShape.unboundedNat x.getString)
      | _ => throwErrorAt b "unsupported binder shape"
    let inner ← elabProp (vars ++ (bs.map (·.name)).toList) body
    let allBounded := inner.allBounded && bs.all (·.isRanged)
    let prop ← bs.foldrM (init := inner.prop) fun b acc => do
      match b with
      | .ranged x lo hi =>
        `(ballIco $(← tsIntLitToTerm lo) $(← tsIntLitToTerm hi)
            (fun $(mkIdent (Name.mkSimple x)) => $acc))
      | .unboundedInt x =>
        `(∀ ($(mkIdent (Name.mkSimple x)) : Int), $acc)
      | .unboundedNat x =>
        `(∀ ($(mkIdent (Name.mkSimple x)) : Int),
            0 ≤ $(mkIdent (Name.mkSimple x)) → $acc)
    let search ←
      if allBounded then
        bs.foldrM (init := inner.search) fun b acc => do
          match b with
          | .ranged x lo hi =>
            `(findCexIco $(← tsIntLitToTerm lo) $(← tsIntLitToTerm hi)
                (fun $(mkIdent (Name.mkSimple x)) => $acc))
          | _ => pure acc
      else
        `((none : Option (List Int)))
    return ⟨prop, search, (bs.map (·.name)).toList ++ inner.names, allBounded⟩
  | stx => throwErrorAt stx "unsupported property shape"

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
names. Best-effort: any failure — a value the readback does not recognize —
degrades to `none` instead of escaping; only a blown heartbeat budget
propagates, as the annotation's Timeout. -/
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
    (fun ex => if ex.isMaxHeartbeat then throw ex else return none)

/-- After the kernel rejects a decide proof, reduce the `Decidable` instance
to tell a false property from one the kernel could not evaluate. The instance
is re-synthesized from the proposition so nothing depends on the proof term's
internal shape; the reduction is best-effort — failures degrade to `none`,
except a blown heartbeat budget, which propagates as the annotation's
Timeout. Established falsity is terminal: with binders and a searched-out
witness it ships as `CounterSatisfiable`, otherwise as a false-on-domain
`GaveUp`. `none` means the instance stayed stuck — the generic stage still
gets its turn. -/
def diagnoseDecideFailure (identity : Identity) (p : Expr)
    (names : List String) (searchStx : TSyntax `term) :
    Term.TermElabM (Option Verdict) := do
  let falseOnDomain : Verdict := ⟨identity, "GaveUp",
    "the property is false on its bounded domain", none⟩
  tryCatchRuntimeEx
    (do
      let inst ← Meta.synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← Meta.withAtLeastTransparency .default <| Meta.whnf inst
      if r.isAppOf ``Decidable.isFalse then
        if names.isEmpty then return some falseOnDomain
        if let some cex ← extractWitness names searchStx then
          return some ⟨identity, "CounterSatisfiable",
            "the property is false on its bounded domain", some cex⟩
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

def attemptDecide (identity : Identity) (p : Expr)
    (searchStx : TSyntax `term) (names : List String) :
    Term.TermElabM (Option Verdict) := do
  let some proof ← (try some <$> Meta.mkDecideProof p catch _ => pure none)
    -- decide could not even build its proof; the generic stage still gets
    -- its turn.
    | return none
  try
    let thmName ← addTheoremSync identity p proof
    -- Reasons name the rung's class, never the tactic: dischargers may change.
    return some ⟨identity, "Theorem",
      "proved by a decision procedure over the bounded domain, " ++
        s!"kernel-checked as {thmName}", none⟩
  catch ex =>
    if ← isKernelTimeout ex then throw ex
    return (← diagnoseDecideFailure identity p names searchStx)

/-- Rung 2's outcome: a verdict, or the state rung 3 continues from — the
root metavariable still linked to the unsolved residual goal. -/
inductive GenericOutcome where
  | done (v : Verdict)
  | stuck (root : Expr) (goal : MVarId) (residual : Expr)

/-- Certifies a closed root metavariable through the kernel; anything off
about the proof (kernel budget exhaustion aside) degrades to the
residual-goal GaveUp rather than escaping. -/
def certifyRoot (identity : Identity) (p root residual : Expr) :
    Term.TermElabM Verdict := do
  let gaveUp : Verdict :=
    ⟨identity, "GaveUp", s!"unsolved goal: {← Meta.ppExpr residual}", none⟩
  let proof ← instantiateMVars root
  if proof.hasExprMVar then return gaveUp
  try
    let thmName ← addTheoremSync identity p proof
    return ⟨identity, "Theorem",
      "proved by generic proof search, " ++
        s!"kernel-checked as {thmName}", none⟩
  catch ex =>
    if ← isKernelTimeout ex then throw ex
    return gaveUp

/-- Rung 2, the generic stage: normalize with the `thales_norm` simp set,
then close with omega. Success is kernel-checked like the decide rung; a
closer that fails leaves the residual goal — rolled back to its
pre-closer state — for the next rung. -/
def attemptGeneric (identity : Identity) (p : Expr) :
    Term.TermElabM GenericOutcome := do
  let mvar ← Meta.mkFreshExprMVar p
  let some ext ← Meta.getSimpExtension? `thales_norm
    | return .done ⟨identity, "Error",
      "the prover's normalization rules are not registered", none⟩
  let ctx ← Meta.Simp.mkContext (config := {})
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← Meta.getSimpCongrTheorems)
  let simped ←
    try Meta.simpGoal mvar.mvarId! ctx
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

/-- Rung 3: grind on the residual goal rung 2 left. Success certifies
through the root metavariable like every rung; failure — its own window's
exhaustion included — ships the residual-goal GaveUp. -/
def attemptGrind (identity : Identity) (p root : Expr) (goal : MVarId)
    (residual : Expr) : Term.TermElabM Verdict := do
  let solved ← tryCatchRuntimeEx
    (try
      let params ← Meta.Grind.mkDefaultParams {}
      let result ← Meta.Grind.main goal params
      pure !result.hasFailed
    catch _ => pure false)
    (fun ex => if ex.isMaxHeartbeat then pure false else throw ex)
  if solved then return ← certifyRoot identity p root residual
  return ⟨identity, "GaveUp", s!"unsolved goal: {← Meta.ppExpr residual}", none⟩

def timeoutVerdict (identity : Identity) (budget : Nat) : Verdict :=
  ⟨identity, "Timeout",
    s!"the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = {budget})", none⟩

def attemptLadder (identity : Identity) (propStx : TSyntax `term)
    (searchStx : TSyntax `term) (names : List String) (allBounded : Bool)
    (budget : Nat) : Term.TermElabM Verdict := do
  let p ←
    try
      withHeartbeats budget <| Term.withoutErrToSorry do
        let p ← Term.elabTerm propStx (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars p
    catch ex =>
      return ⟨identity, "Error",
        s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
  -- Each rung runs under its own fresh window: the kernel overshoots a
  -- shared window by a large factor before its own counter fires, which
  -- would let an early rung's blowout starve the ones after it. Bounded
  -- domains give decide half and each later rung a quarter; unbounded
  -- ones split the budget between the generic and grind rungs.
  let half := max (budget / 2) 1
  let lateShare := if allBounded then max (budget / 4) 1 else half
  let mut starved := false
  if allBounded then
    let outcome ← tryCatchRuntimeEx
      (some <$> withHeartbeats half (attemptDecide identity p searchStx names))
      (fun ex => do
        if ex.isMaxHeartbeat || (← isKernelTimeout ex) then pure none else throw ex)
    match outcome with
    | some (some v) => return v
    | some none => pure ()
    | none => starved := true
  let outcome ← tryCatchRuntimeEx
    (some <$> withHeartbeats lateShare (attemptGeneric identity p))
    (fun ex => do
      if ex.isMaxHeartbeat || (← isKernelTimeout ex) then pure none else throw ex)
  let v ← match outcome with
    | some (.done v) => pure v
    | some (.stuck root goal residual) =>
      withHeartbeats lateShare (attemptGrind identity p root goal residual)
    | none => do
      starved := true
      -- Rung 2 blew its window without leaving a residual; grind starts
      -- over from the original proposition.
      let root ← Meta.mkFreshExprMVar p
      withHeartbeats lateShare (attemptGrind identity p root root.mvarId! p)
  -- A starved earlier rung might have closed the goal given budget, so
  -- exhaustion plus a residual goal is budget exhaustion, not a dead end.
  if starved && v.szs == "GaveUp" then
    return timeoutVerdict identity budget
  return v

elab_rules : command
  | `(#thales_prove $file:str $fn:str $prop:str $[:= $p:ts_prop]?) => do
    let identity : Identity := ⟨file.getString, fn.getString, prop.getString⟩
    -- A failed ts_def blocks the annotation only when nothing modeled the
    -- name: an overload signature fails while the implementation models.
    -- Unmapped construct ⇒ Inappropriate, anything else ⇒ Error.
    if (findModel? (← getEnv) fn.getString).isNone then
      if let some failed := findFailed? (← getEnv) fn.getString then
        let szs := if failed.construct.isSome then "Inappropriate" else "Error"
        return ← Verdict.emit
          ⟨identity, szs, s!"'{fn.getString}' could not be modeled: {failed.reason}", none⟩
    let verdict : Verdict ←
      match p with
      | none => pure ⟨identity, "NotTried", "stub: no structured property provided", none⟩
      | some p =>
        if let some reason := propInappropriate? (← getEnv) p then
          pure ⟨identity, "Inappropriate", reason, none⟩
        else
          try
            let ep ← elabProp [] p
            let budget := thales.heartbeats.get (← getOptions)
            -- The ladder caps each of its phases at the budget (or a split
            -- share of it); a blown cap anywhere in the attempt — the
            -- kernel's decide evaluation included — is this annotation's
            -- Timeout, never the file's failure.
            liftTermElabM <|
              tryCatchRuntimeEx
                (attemptLadder identity ep.prop ep.search ep.names ep.allBounded budget)
                fun ex => do
                  unless ex.isMaxHeartbeat || (← isKernelTimeout ex) do throw ex
                  pure (timeoutVerdict identity budget)
          catch ex =>
            pure ⟨identity, "Error",
              s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
    verdict.emit

end ThalesDsl
