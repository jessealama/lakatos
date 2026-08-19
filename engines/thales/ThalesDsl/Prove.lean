import Lean
import ThalesDsl.Verdict
import ThalesDsl.Model

namespace ThalesDsl

open Lean Elab Command

/-- Transcribes a `ts_prop` into a Lean `Prop` term: bounded binders become
nested `ballIco`, `≡` equations compare `TsM Int` results, boolean islands
must evaluate to `pure true`. -/
partial def elabProp (vars : List String) : TSyntax `ts_prop → CommandElabM (TSyntax `term)
  | `(ts_prop| ts.eq($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .int l
    let rt ← evalExpr vars .int r
    `(($lt : TsM Int) = $rt)
  | `(ts_prop| ts.istrue($e:ts_expr)) => do
    let t ← evalExpr vars .bool e
    `(($t : TsM Bool) = pure true)
  | `(ts_prop| ts.forall($binders:ts_binder,*) {$body:ts_prop}) => do
    let bs ← binders.getElems.mapM fun b => match b with
      | `(ts_binder| ts.binder[$x:str](ts.int, ts.range($lo:tsIntLit, $hi:tsIntLit))) =>
        pure (x.getString, lo, hi)
      | _ => throwErrorAt b "unsupported binder shape"
    let inner ← elabProp (vars ++ (bs.map (·.1)).toList) body
    bs.foldrM (init := inner) fun (x, lo, hi) acc => do
      `(ballIco $(← tsIntLitToTerm lo) $(← tsIntLitToTerm hi)
          (fun $(mkIdent (Name.mkSimple x)) => $acc))
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

/-- After the kernel rejects a decide proof, reduce the `Decidable` instance
to tell a false property from one the kernel could not evaluate. The instance
is re-synthesized from the proposition so nothing depends on the proof term's
internal shape; the reduction is best-effort — heartbeat exhaustion degrades
to the stuck verdict instead of escaping. -/
def diagnoseDecideFailure (identity : Identity) (p : Expr) : Term.TermElabM Verdict := do
  let stuck : Verdict := ⟨identity, "GaveUp",
    "the property did not evaluate to a truth value on its bounded domain"⟩
  tryCatchRuntimeEx
    (do
      let inst ← Meta.synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← Meta.withAtLeastTransparency .default <| Meta.whnf inst
      if r.isAppOf ``Decidable.isFalse then
        return ⟨identity, "GaveUp", "the property is false on its bounded domain"⟩
      return stuck)
    (fun _ => return stuck)

def attemptDecide (identity : Identity) (thmName : Name) (propStx : TSyntax `term) :
    Term.TermElabM Verdict := do
  let p ←
    try
      Term.withoutErrToSorry do
        let p ← Term.elabTerm propStx (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars p
    catch ex =>
      return ⟨identity, "Error",
        s!"property elaboration failed: {← ex.toMessageData.toString}"⟩
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
      return (← diagnoseDecideFailure identity p)
    return ⟨identity, "Theorem", s!"proved by decide, kernel-checked as {thmName}"⟩
  catch ex =>
    return ⟨identity, "GaveUp", s!"decide failed: {← ex.toMessageData.toString}"⟩

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
          ⟨identity, szs, s!"'{fn.getString}' could not be modeled: {failed.reason}"⟩
    let verdict : Verdict ←
      match p with
      | none => pure ⟨identity, "NotTried", "stub: no structured property provided"⟩
      | some p =>
        if let some reason := propInappropriate? (← getEnv) p then
          pure ⟨identity, "Inappropriate", reason⟩
        else
          try
            let propStx ← elabProp [] p
            let thmName := freshTheoremName (← getEnv) identity
            liftTermElabM (attemptDecide identity thmName propStx)
          catch ex =>
            pure ⟨identity, "Error",
              s!"property elaboration failed: {← ex.toMessageData.toString}"⟩
    verdict.emit

end ThalesDsl
