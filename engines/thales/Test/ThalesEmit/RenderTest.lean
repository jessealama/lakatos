import ThalesEmit

open Lean ThalesEmit

-- Schema violations decode to errors naming the offender, never to
-- defaults.
#guard (decodeEmission (Json.mkObj [])) matches .error _
#guard
  (decodeEmission (Json.mkObj
    [("file", "t.ts"), ("declarations", Json.arr #[Json.mkObj [("kind", "class")]]),
     ("obligations", Json.arr #[])]))
  matches .error "unknown declaration kind 'class'"

-- The pinned tracer emission renders to the golden artifact — the file a
-- human inspected and accepted. #eval runs CoreM inside this module's own
-- environment, which imports ThalesDsl transitively, so the printer has
-- its syntax tables. Paths are relative to engines/thales, where every
-- lake invocation runs.
#eval show CoreM Unit from do
  let text ← IO.FS.readFile "tests/fixtures/tracer.emission.json"
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let rendered ← renderEmission e
  let expected ← IO.FS.readFile "tests/fixtures/tracer.emitted.lean.expected"
  unless rendered == expected do
    throwError "rendered artifact drifted from the golden file:\n{rendered}"

-- A shape outside the slice is refused with a message naming the gap.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "f", params := #["x"], source := "f",
                        body := #[.ret (.id "x"), .ret (.id "x")] }]
    obligations := #[] }
  let refused ← try
    let _ ← renderEmission e
    pure false
  catch _ => pure true
  unless refused do
    throwError "a multi-statement body was rendered instead of refused"
