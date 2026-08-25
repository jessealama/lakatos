import ThalesEmit.Json
import ThalesEmit.Render

/-! The `thales-emit` executable: one emission JSON in, one readable
`.lean` artifact out. Any failure — unreadable file, schema mismatch, a
shape outside the slice — is one message on stderr and exit 1; the
artifact is only written whole. -/

open Lean ThalesEmit

unsafe def main (args : List String) : IO UInt32 := do
  let [inPath, outPath] := args
    | IO.eprintln "usage: thales-emit <emission.json> <out.lean>"
      return 1
  try
    let text ← IO.FS.readFile inPath
    let emission ←
      match Json.parse text >>= decodeEmission with
      | .error msg =>
        IO.eprintln s!"thales-emit: {inPath}: {msg}"
        return 1
      | .ok e => pure e
    initSearchPath (← findSysroot)
    let out ← withImportModules #[{ module := `ThalesDsl }] {} (trustLevel := 0)
      fun env => do
        let ctx : Core.Context := { fileName := "<thales-emit>", fileMap := default }
        let (out, _) ← (renderEmission emission).toIO ctx { env }
        pure out
    IO.FS.writeFile outPath out
    return 0
  catch ex =>
    IO.eprintln s!"thales-emit: {ex}"
    return 1
