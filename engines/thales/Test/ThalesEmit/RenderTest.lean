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

-- The unary-operator and binder-domain IR decodes strictly.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "unop"), ("op", "-"), ("operand", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.unop "-" (.id "x"))
#guard
  (decodeBinder (Json.mkObj [("name", "x"), ("kind", "int")]))
  matches .ok (.int "x")
#guard
  (decodeBinder (Json.mkObj [("name", "n"), ("kind", "nat")]))
  matches .ok (.nat "n")
#guard
  (decodeBinder (Json.mkObj
    [("name", "x"), ("kind", "range"), ("lo", "0"), ("hi", "10")]))
  matches .ok (.range "x" 0 10)
#guard (decodeBinder (Json.mkObj [("name", "x"), ("kind", "real")])) matches .error _

-- The pinned emissions render to the golden artifacts — files a human
-- inspected and accepted. #eval runs CoreM inside this module's own
-- environment, which imports ThalesDsl transitively, so the printer has
-- its syntax tables. Paths are relative to engines/thales, where every
-- lake invocation runs.
def goldenCheck (emissionPath expectedPath : String) : CoreM Unit := do
  let text ← IO.FS.readFile emissionPath
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let rendered ← renderEmission e
  let expected ← IO.FS.readFile expectedPath
  unless rendered == expected do
    throwError "rendered artifact drifted from the golden file:\n{rendered}"

#eval goldenCheck "tests/fixtures/tracer.emission.json"
  "tests/fixtures/tracer.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/operators.emission.json"
  "tests/fixtures/operators.emitted.lean.expected"

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
