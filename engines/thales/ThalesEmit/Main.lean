import ThalesEmit.Json
import ThalesEmit.Render
import ThalesEmit.Artifact

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
    -- Extension state, the parser and printer tables among it, is loaded
    -- only on demand, and loading it runs the imported initializers.
    enableInitializersExecution
    let env ← importModules #[{ module := `ThalesDsl }, { module := `ThalesEmit }] {}
      (trustLevel := 0) (loadExts := true)
    let ctx : Core.Context := { fileName := "<thales-emit>", fileMap := default }
    let (out, _) ← (renderEmission emission).toIO ctx { env }
    IO.FS.writeFile outPath out
    return 0
  catch ex =>
    IO.eprintln s!"thales-emit: {ex}"
    return 1
