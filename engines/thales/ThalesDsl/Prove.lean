import Lean
import ThalesDsl.Verdict

namespace ThalesDsl

open Lean Elab Command

/-- States a per-annotation proof obligation and reports its verdict as one
JSON line on stdout. Stub: the proof ladder is not implemented yet, so
healthy commands report `NotTried`. The optional trailing term stands in
for future elaboration work; its failure must be contained to this
command's verdict line. -/
syntax "#thales_prove " str str str (" := " term)? : command

elab_rules : command
  | `(#thales_prove $file:str $fn:str $prop:str $[:= $t:term]?) => do
    let identity : Identity := ⟨file.getString, fn.getString, prop.getString⟩
    let verdict : Verdict ←
      try
        if let some t := t then
          -- withoutErrToSorry: elaboration failures must throw (and be caught
          -- here), not recover to sorry and leak diagnostics onto stdout.
          liftTermElabM <| Term.withoutErrToSorry do
            discard <| Term.elabTerm t none
            Term.synthesizeSyntheticMVarsNoPostponing
        pure ⟨identity, "NotTried", "stub: proof ladder not yet implemented"⟩
      catch e =>
        pure ⟨identity, "Error", s!"elaboration failed: {← e.toMessageData.toString}"⟩
    verdict.emit

end ThalesDsl
