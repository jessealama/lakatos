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

-- Emitted defs live under the model namespace: a TS function named
-- after a root-level Lean name (`id`) must still define.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "id", params := #["x"], source := "id",
                        body := #[.ret (.id "x")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.id ").length == 2 do
    throwError "the emitted def is not namespaced:\n{rendered}"

-- The artifact is re-parsed plain text: a binder named after the
-- function it calls must not capture the call.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "bump", params := #["x"], source := "bump",
                        body := #[.ret (.binop "+" (.id "x") (.num "1"))] }]
    obligations := #[{ function := "bump", property := "p", formula := "f",
                       payload := .structured #[.int "bump"]
                         (.eq (.call "bump" #[.id "bump"])
                              (.call "bump" #[.id "bump"])) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "TsModel.bump (Float.ofInt bump)").length == 3 do
    throwError "the call is exposed to binder capture:\n{rendered}"

-- A binder named after the emitted vocabulary itself (`pure`) is primed,
-- keeping the annotation provable instead of capturing the leaf.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "f", params := #["x"], source := "f",
                        body := #[.ret (.id "x")] }]
    obligations := #[{ function := "f", property := "p", formula := "f",
                       payload := .structured #[.int "pure"]
                         (.istrue (.binop ">=" (.call "f" #[.id "pure"])
                                             (.num "0"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "pure'").length == 3 do
    throwError "the reserved binder name is not primed:\n{rendered}"

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
