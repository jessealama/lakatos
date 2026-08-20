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

def attemptDecide (identity : Identity) (thmName : Name) (p : Expr)
    (searchStx : TSyntax `term) (names : List String) :
    Term.TermElabM (Option Verdict) := do
  try
    let proof ← Meta.mkDecideProof p
    -- addDecl's kernel check is asynchronous by default, landing after the
    -- verdict ships. Disable async (as `decide +kernel` does) so the kernel
    -- evaluates the proof here: a false property is a catchable failure,
    -- not a late artifact failure, and the success path pays for exactly
    -- one evaluation.
    try
      withOptions (Elab.async.set · false) do
        addDecl (.thmDecl { name := thmName, levelParams := [], type := p, value := proof })
    catch _ =>
      return (← diagnoseDecideFailure identity p names searchStx)
    return some ⟨identity, "Theorem", s!"proved by decide, kernel-checked as {thmName}", none⟩
  catch _ =>
    -- decide could not even build its proof; the generic stage still gets
    -- its turn.
    return none

/-- Rung 2, the generic stage: normalize with the `thales_norm` simp set,
then close with omega. Success is kernel-checked like the decide rung;
failure reports the residual goal — what actually stumped the prover. -/
def attemptGeneric (identity : Identity) (thmName : Name) (p : Expr) :
    Term.TermElabM Verdict := do
  let mvar ← Meta.mkFreshExprMVar p
  let some ext ← Meta.getSimpExtension? `thales_norm
    | return ⟨identity, "Error", "the thales_norm simp set is not registered", none⟩
  let ctx ← Meta.Simp.mkContext (config := {})
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← Meta.getSimpCongrTheorems)
  let gaveUp (residual : Expr) : Term.TermElabM Verdict := do
    return ⟨identity, "GaveUp", s!"unsolved goal: {← Meta.ppExpr residual}", none⟩
  -- Ships the assembled proof through the kernel; anything off about it
  -- degrades to the residual-goal GaveUp rather than escaping.
  let certify (residual : Expr) : Term.TermElabM Verdict := do
    let proof ← instantiateMVars mvar
    if proof.hasExprMVar then return ← gaveUp residual
    try
      withOptions (Elab.async.set · false) do
        addDecl (.thmDecl { name := thmName, levelParams := [], type := p, value := proof })
      return ⟨identity, "Theorem",
        s!"proved by simp/omega, kernel-checked as {thmName}", none⟩
    catch _ => gaveUp residual
  let simped ←
    try Meta.simpGoal mvar.mvarId! ctx
    catch _ => pure (some (#[], mvar.mvarId!), {})
  match simped.1 with
  | none => certify p
  | some (_, g) =>
    let residual ← instantiateMVars (← g.getType)
    try
      match ← g.falseOrByContra with
      | none => certify residual
      | some gFalse =>
        gFalse.withContext do
          Tactic.Omega.omega (← getLocalHyps).toList gFalse {}
        certify residual
    catch _ => gaveUp residual

def attemptLadder (identity : Identity) (thmName : Name) (propStx : TSyntax `term)
    (searchStx : TSyntax `term) (names : List String) (allBounded : Bool) :
    Term.TermElabM Verdict := do
  let p ←
    try
      Term.withoutErrToSorry do
        let p ← Term.elabTerm propStx (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars p
    catch ex =>
      return ⟨identity, "Error",
        s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
  if allBounded then
    if let some v ← attemptDecide identity thmName p searchStx names then
      return v
  attemptGeneric identity thmName p

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
            let thmName := freshTheoremName (← getEnv) identity
            let budget := thales.heartbeats.get (← getOptions)
            -- One fresh, capped budget per annotation; a blown budget
            -- anywhere in the attempt — the kernel's decide evaluation
            -- included — is this annotation's Timeout, never the file's
            -- failure.
            liftTermElabM <|
              withHeartbeats budget <|
                tryCatchRuntimeEx
                  (attemptLadder identity thmName ep.prop ep.search ep.names ep.allBounded)
                  fun ex => do
                    unless ex.isMaxHeartbeat do throw ex
                    pure ⟨identity, "Timeout",
                      s!"the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = {budget})", none⟩
          catch ex =>
            pure ⟨identity, "Error",
              s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
    verdict.emit

end ThalesDsl
