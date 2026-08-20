import Lean
import ThalesDsl.Verdict
import ThalesDsl.Model

register_option thales.heartbeats : Nat := {
  defValue := 200000
  descr := "per-annotation heartbeat budget for #thales_prove, in the maxHeartbeats unit; an attempt that exceeds it reports a Timeout verdict"
}

namespace ThalesDsl

open Lean Elab Command

/-- Transcribes a `ts_prop` into a Lean `Prop` term — bounded binders become
nested `ballIco`, `≡` equations compare `TsM Int` results, boolean islands
must evaluate to `pure true` — plus a parallel witness-search term of type
`Option (List Int)` (one `findCexIco` per binder, a decidable test at the
leaf) and the binder names in binder order. -/
partial def elabProp (vars : List String) :
    TSyntax `ts_prop → CommandElabM (TSyntax `term × TSyntax `term × List String)
  | `(ts_prop| ts.eq($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .int l
    let rt ← evalExpr vars .int r
    let prop ← `(($lt : TsM Int) = $rt)
    let search ← `(if ($lt : TsM Int) = $rt then (none : Option (List Int)) else some [])
    return (prop, search, [])
  | `(ts_prop| ts.istrue($e:ts_expr)) => do
    let t ← evalExpr vars .bool e
    let prop ← `(($t : TsM Bool) = pure true)
    let search ← `(if ($t : TsM Bool) = pure true then (none : Option (List Int)) else some [])
    return (prop, search, [])
  | `(ts_prop| ts.forall($binders:ts_binder,*) {$body:ts_prop}) => do
    let bs ← binders.getElems.mapM fun b => match b with
      | `(ts_binder| ts.binder[$x:str](ts.int, ts.range($lo:tsIntLit, $hi:tsIntLit))) =>
        pure (x.getString, lo, hi)
      | _ => throwErrorAt b "unsupported binder shape"
    let (innerProp, innerSearch, innerNames) ←
      elabProp (vars ++ (bs.map (·.1)).toList) body
    let prop ← bs.foldrM (init := innerProp) fun (x, lo, hi) acc => do
      `(ballIco $(← tsIntLitToTerm lo) $(← tsIntLitToTerm hi)
          (fun $(mkIdent (Name.mkSimple x)) => $acc))
    let search ← bs.foldrM (init := innerSearch) fun (x, lo, hi) acc => do
      `(findCexIco $(← tsIntLitToTerm lo) $(← tsIntLitToTerm hi)
          (fun $(mkIdent (Name.mkSimple x)) => $acc))
    return (prop, search, (bs.map (·.1)).toList ++ innerNames)
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
internal shape; the reduction is best-effort — failures degrade to the stuck
verdict, except a blown heartbeat budget, which propagates as the
annotation's Timeout. A false property with binders gets
its witness searched out and ships as `CounterSatisfiable`; without binders
(or when extraction degrades) falsity stays a `GaveUp`. -/
def diagnoseDecideFailure (identity : Identity) (p : Expr)
    (names : List String) (searchStx : TSyntax `term) : Term.TermElabM Verdict := do
  let stuck : Verdict := ⟨identity, "GaveUp",
    "the property did not evaluate to a truth value on its bounded domain", none⟩
  let falseOnDomain : Verdict := ⟨identity, "GaveUp",
    "the property is false on its bounded domain", none⟩
  tryCatchRuntimeEx
    (do
      let inst ← Meta.synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← Meta.withAtLeastTransparency .default <| Meta.whnf inst
      if r.isAppOf ``Decidable.isFalse then
        if names.isEmpty then return falseOnDomain
        if let some cex ← extractWitness names searchStx then
          return ⟨identity, "CounterSatisfiable",
            "the property is false on its bounded domain", some cex⟩
        return falseOnDomain
      return stuck)
    (fun ex => if ex.isMaxHeartbeat then throw ex else return stuck)

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

def attemptDecide (identity : Identity) (thmName : Name) (propStx : TSyntax `term)
    (searchStx : TSyntax `term) (names : List String) :
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
    return ⟨identity, "Theorem", s!"proved by decide, kernel-checked as {thmName}", none⟩
  catch ex =>
    return ⟨identity, "GaveUp", s!"decide failed: {← ex.toMessageData.toString}", none⟩

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
            let (propStx, searchStx, names) ← elabProp [] p
            let thmName := freshTheoremName (← getEnv) identity
            let budget := thales.heartbeats.get (← getOptions)
            -- One fresh, capped budget per annotation; a blown budget
            -- anywhere in the attempt — the kernel's decide evaluation
            -- included — is this annotation's Timeout, never the file's
            -- failure.
            liftTermElabM <|
              withHeartbeats budget <|
                tryCatchRuntimeEx
                  (attemptDecide identity thmName propStx searchStx names)
                  fun ex => do
                    unless ex.isMaxHeartbeat do throw ex
                    pure ⟨identity, "Timeout",
                      s!"the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = {budget})", none⟩
          catch ex =>
            pure ⟨identity, "Error",
              s!"property elaboration failed: {← ex.toMessageData.toString}", none⟩
    verdict.emit

end ThalesDsl
