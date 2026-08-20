import Lean
import ThalesDsl.Verdict
import ThalesDsl.Model

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

/-- One parsed ∀-binder: its variable, plus the range when bounded. -/
inductive BinderShape where
  | ranged (x : String) (lo hi : TSyntax ``tsIntLit)
  | unboundedInt (x : String)
  | unboundedNat (x : String)
  /-- A `number` binder: no enumeration, only the bounds it carries as
  hypotheses. Each bound is its comparison operator and its endpoint. -/
  | number (x : String)
      (lower : Option (String × TSyntax ``tsFloatLit))
      (upper : Option (String × TSyntax ``tsFloatLit))

def BinderShape.name : BinderShape → String
  | .ranged x .. | .unboundedInt x | .unboundedNat x | .number x .. => x

def BinderShape.isRanged : BinderShape → Bool
  | .ranged .. => true
  | _ => false

/-- The value of an endpoint literal, for sizing the enumeration. -/
def tsIntLitValue : TSyntax ``tsIntLit → CommandElabM Int
  | `(tsIntLit| $n:num) => pure (Int.ofNat n.getNat)
  | `(tsIntLit| -$n:num) => pure (-(Int.ofNat n.getNat))
  | stx => throwErrorAt stx "malformed integer literal"

/-- What elabProp builds from a ts_prop. `allBounded` gates the decide
rung: without it no Decidable instance exists, and `search` is a stub —
witness search never runs on unbounded domains. `domainSize` is how many
assignments that enumeration would visit, meaningful only when
`allBounded`; it is what the evaluation tier is capped against. -/
structure ElabProp where
  prop : TSyntax `term
  search : TSyntax `term
  names : List String
  allBounded : Bool
  domainSize : Nat

/-- Transcribes a `ts_prop` into a Lean `Prop` term — bounded binders become
nested `ballIco`, unbounded int/nat binders plain `∀`s (nat carries its
nonnegativity hypothesis) whose values coerce into the Float body at the
call boundary, `≡` equations compare `TsM Float` results, boolean
islands must evaluate to `pure true` — plus a parallel witness-search term
of type `Option (List Int)` (one `findCexIco` per binder, a decidable test
at the leaf) and the binder names in binder order. -/
partial def elabProp (vars : List String) :
    TSyntax `ts_prop → CommandElabM ElabProp
  | `(ts_prop| ts.eq($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .num l
    let rt ← evalExpr vars .num r
    -- `≡` is SameValue — the relation the refuter runs as `Object.is` —
    -- which is exactly Lean's propositional equality on Float. `===` is
    -- IEEE and lives in evalExpr as Float.beq.
    let prop ← `(($lt : TsM Float) = $rt)
    let search ← `(if ($lt : TsM Float) = $rt then (none : Option (List Int)) else some [])
    return ⟨prop, search, [], true, 1⟩
  | `(ts_prop| ts.istrue($e:ts_expr)) => do
    let t ← evalExpr vars .bool e
    let prop ← `(($t : TsM Bool) = pure true)
    let search ← `(if ($t : TsM Bool) = pure true then (none : Option (List Int)) else some [])
    return ⟨prop, search, [], true, 1⟩
  | `(ts_prop| ts.forall($binders:ts_binder,*) {$body:ts_prop}) => do
    let bs ← binders.getElems.mapM fun b => match b with
      | `(ts_binder| ts.binder[$x:str](ts.int, ts.range($lo:tsIntLit, $hi:tsIntLit))) =>
        pure (BinderShape.ranged x.getString lo hi)
      | `(ts_binder| ts.binder[$x:str](ts.int)) =>
        pure (BinderShape.unboundedInt x.getString)
      | `(ts_binder| ts.binder[$x:str](ts.nat)) =>
        pure (BinderShape.unboundedNat x.getString)
      | `(ts_binder| ts.binder[$x:str](ts.number $[, $bs:ts_bound]*)) => do
        let mut lower : Option (String × TSyntax ``tsFloatLit) := none
        let mut upper : Option (String × TSyntax ``tsFloatLit) := none
        for b in bs do
          match b with
          | `(ts_bound| ts.lower[$op:str](ts.fnum[$lit:tsFloatLit])) =>
            if lower.isSome then throwErrorAt b "duplicate lower bound"
            lower := some (op.getString, lit)
          | `(ts_bound| ts.upper[$op:str](ts.fnum[$lit:tsFloatLit])) =>
            if upper.isSome then throwErrorAt b "duplicate upper bound"
            upper := some (op.getString, lit)
          | _ => throwErrorAt b "unsupported bound shape"
        pure (BinderShape.number x.getString lower upper)
      | _ => throwErrorAt b "unsupported binder shape"
    let inner ← elabProp (vars ++ (bs.map (·.name)).toList) body
    let allBounded := inner.allBounded && bs.all (·.isRanged)
    -- The enumeration variable is an Int; the body is Float-valued. The
    -- coercion is a beta-redex rather than a `let` so every rung reduces it
    -- the same way. `Float.ofInt` is injective on the clamped domain, which
    -- is what makes the transcriber's safe-integer clamp load-bearing.
    let coerced (x : String) (iv : Ident) (body : TSyntax `term) :
        CommandElabM (TSyntax `term) :=
      `((fun ($(mkIdent (Name.mkSimple x)) : Float) => $body) (Float.ofInt $iv))
    let prop ← bs.foldrM (init := inner.prop) fun b acc => do
      let iv := mkIdent (Name.mkSimple s!"ts#int{b.name}")
      match b with
      | .ranged x lo hi =>
        `(ballIco $(← tsIntLitToInt lo) $(← tsIntLitToInt hi)
            (fun ($iv : Int) => $(← coerced x iv acc)))
      | .unboundedInt x =>
        `(∀ ($iv : Int), $(← coerced x iv acc))
      | .unboundedNat x =>
        `(∀ ($iv : Int), 0 ≤ $iv → $(← coerced x iv acc))
      | .number x lower upper =>
        -- Already a Float, so no coercion, and never enumerated: the binder
        -- is its type plus whichever bounds it carries as hypotheses.
        let v := mkIdent (Name.mkSimple x)
        let mut body := acc
        if let some (op, lit) := upper then
          let e ← tsFloatLitToTerm lit
          let hyp ← match op with
            | "<" => `($v < $e)
            | "<=" => `($v ≤ $e)
            | other => throwErrorAt lit s!"unsupported upper bound '{other}'"
          body ← `($hyp → $body)
        if let some (op, lit) := lower then
          let e ← tsFloatLitToTerm lit
          let hyp ← match op with
            | "<" => `($e < $v)
            | "<=" => `($e ≤ $v)
            | other => throwErrorAt lit s!"unsupported lower bound '{other}'"
          body ← `($hyp → $body)
        `(∀ ($v : Float), $body)
    let search ←
      if allBounded then
        bs.foldrM (init := inner.search) fun b acc => do
          match b with
          | .ranged x lo hi =>
            let iv := mkIdent (Name.mkSimple s!"ts#int{x}")
            `(findCexIco $(← tsIntLitToInt lo) $(← tsIntLitToInt hi)
                (fun ($iv : Int) => $(← coerced x iv acc)))
          | _ => pure acc
      else
        `((none : Option (List Int)))
    -- How many assignments the enumeration would visit. An empty range
    -- contributes 0, which is exactly right: nothing to evaluate.
    let mut domainSize := inner.domainSize
    for b in bs do
      if let .ranged _ lo hi := b then
        domainSize := domainSize * ((← tsIntLitValue hi) - (← tsIntLitValue lo)).toNat
    return ⟨prop, search, (bs.map (·.name)).toList ++ inner.names,
      allBounded, domainSize⟩
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
    "the property is false on its bounded domain", none⟩
  tryCatchRuntimeEx
    (do
      let inst ← Meta.synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← Meta.withAtLeastTransparency .default <| Meta.whnf inst
      if r.isAppOf ``Decidable.isFalse then
        if names.isEmpty then return some falseOnDomain
        if let some cex ← extractWitness names searchStx then
          return some ⟨identity, .CounterSatisfiable,
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

/-- The axioms every Lean proof may use without extending the trusted base. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- A proved annotation's reason. `method` names the rung's class — never a
tactic, since dischargers change — but the trust level is read off the
theorem's actual axioms rather than asserted by the rung, which could drift
from what happened. Any axiom beyond the standard three means the result
rests on more than the kernel; today that is native evaluation, which trusts
the compiler and the host's floating point unit. -/
def proofReason (method : String) (thmName : Name) : Term.TermElabM String := do
  let axioms ← collectAxioms thmName
  let extra := axioms.filter (!standardAxioms.contains ·)
  if extra.isEmpty then
    return s!"proved by {method}, kernel-checked as {thmName}"
  return s!"proved by {method}, admitted as {thmName}; the result is " ++
    s!"trusted from evaluation rather than checked by the kernel"

def attemptDecide (identity : Identity) (p : Expr)
    (searchStx : TSyntax `term) (names : List String) :
    Term.TermElabM (Option Verdict) := do
  let some proof ← (try some <$> Meta.mkDecideProof p catch _ => pure none)
    -- decide could not even build its proof; the generic stage still gets
    -- its turn.
    | return none
  try
    let thmName ← addTheoremSync identity p proof
    return some ⟨identity, .Theorem,
      ← proofReason "a decision procedure over the bounded domain" thmName, none⟩
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
    "the property is false on its bounded domain", none⟩
  let some d ← (try some <$> Meta.mkDecide p catch _ => pure none)
    | return none
  match ← Meta.nativeEqTrue `native_decide d with
  | .notTrue =>
    -- Established falsity is terminal; only the illustration is optional.
    if names.isEmpty then return some falseOnDomain
    if let some cex ← extractWitness names searchStx then
      return some ⟨identity, .CounterSatisfiable,
        "the property is false on its bounded domain", some cex⟩
    return some falseOnDomain
  | .success prf =>
    let inst := d.appArg!
    let proof := mkApp3 (mkConst ``of_decide_eq_true) p inst prf
    let thmName ← addTheoremSync identity p proof
    return some ⟨identity, .Theorem,
      ← proofReason "a decision procedure over the bounded domain" thmName, none⟩

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
    ⟨identity, .GaveUp, s!"unsolved goal: {← Meta.ppExpr residual}", none⟩
  let proof ← instantiateMVars root
  if proof.hasExprMVar then return gaveUp
  try
    let thmName ← addTheoremSync identity p proof
    return ⟨identity, .Theorem, ← proofReason "generic proof search" thmName, none⟩
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
    | return .done ⟨identity, .Error,
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
through the root metavariable like every rung; failure — either resource
limit included — ships the residual-goal GaveUp. -/
def attemptGrind (identity : Identity) (p root : Expr) (goal : MVarId)
    (residual : Expr) : Term.TermElabM Verdict := do
  let solved ← tryCatchRuntimeEx
    (try
      let params ← Meta.Grind.mkDefaultParams {}
      let result ← Meta.Grind.main goal params
      pure !result.hasFailed
    catch _ => pure false)
    (fun ex => if ex.isRuntime then pure false else throw ex)
  if solved then return ← certifyRoot identity p root residual
  return ⟨identity, .GaveUp, s!"unsolved goal: {← Meta.ppExpr residual}", none⟩

def timeoutVerdict (identity : Identity) (budget : Nat) : Verdict :=
  ⟨identity, .Timeout,
    s!"the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = {budget})", none⟩

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
          s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩)
  let p ← match elaborated with
    | .ok p => pure p
    | .error v => return v
  -- Each rung runs under its own fresh window: the kernel overshoots a
  -- shared window by a large factor before its own counter fires, which
  -- would let an early rung's blowout starve the ones after it. Four rungs
  -- now. A bounded run splits the budget evenly across the two decide tiers
  -- and the two symbolic ones; an unbounded run has no decide tier to fund,
  -- so the symbolic rungs take half each. Every share floors at 1, since a
  -- zero budget reads as unlimited.
  let quarter := max (budget / 4) 1
  let half := max (budget / 2) 1
  let decideShare := quarter
  let lateShare := if allBounded then quarter else half
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
    runRung (withHeartbeats lateShare (attemptGeneric identity p))
  if rungStarved then starved := true
  let v ← match outcome with
    | some (.done v) => pure v
    | some (.stuck root goal residual) =>
      withHeartbeats lateShare (attemptGrind identity p root goal residual)
    | none => do
      -- Rung 2 blew a limit without leaving a residual; grind starts over
      -- from the original proposition.
      let root ← Meta.mkFreshExprMVar p
      withHeartbeats lateShare (attemptGrind identity p root root.mvarId! p)
  -- A starved earlier rung might have closed the goal given budget, so
  -- exhaustion plus a residual goal is budget exhaustion, not a dead end.
  if starved && v.szs == .GaveUp then
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
        let szs : Szs := if failed.construct.isSome then .Inappropriate else .Error
        return ← Verdict.emit
          ⟨identity, szs, s!"'{fn.getString}' could not be modeled: {failed.reason}", none⟩
    let verdict : Verdict ←
      match p with
      | none => pure ⟨identity, .NotTried, "stub: no structured property provided", none⟩
      | some p =>
        if let some reason := propInappropriate? (← getEnv) p then
          pure ⟨identity, .Inappropriate, reason, none⟩
        else
          try
            let ep ← elabProp [] p
            -- Floored at 1: maxHeartbeats 0 means unlimited, so a zero
            -- budget would leave the elaboration window uncontained.
            let budget := max (thales.heartbeats.get (← getOptions)) 1
            let evalCap := thales.maxEvaluatedElements.get (← getOptions)
            -- The ladder caps each of its phases at the budget (or a split
            -- share of it); a blown cap anywhere in the attempt — the
            -- kernel's decide evaluation included — is this annotation's
            -- Timeout, never the file's failure. Whatever else escapes the
            -- ladder is contained here too, named for the phase it came
            -- from: this catch is past the point of elaborating anything.
            liftTermElabM <|
              tryCatchRuntimeEx
                (attemptLadder identity ep.prop ep.search ep.names ep.allBounded
                  ep.domainSize budget evalCap)
                fun ex => do
                  if ex.isMaxHeartbeat || (← isKernelTimeout ex) then
                    return timeoutVerdict identity budget
                  return ⟨identity, .Error,
                    s!"proof search failed: {← ex.toMessageData.toString}", none⟩
          catch ex =>
            pure ⟨identity, .Error,
              s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
    verdict.emit

end ThalesDsl
