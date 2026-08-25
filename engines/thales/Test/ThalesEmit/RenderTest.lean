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
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"),
     ("lower", Json.mkObj [("op", "<"), ("lit", "0")]),
     ("upper", Json.mkObj [("op", "<="), ("lit", "1")])]))
  matches .ok (.number "a" (some ("<", "0")) (some ("<=", "1")))
-- An absent side is a missing field, so a rangeless binder decodes bare.
#guard
  (decodeBinder (Json.mkObj [("name", "a"), ("kind", "number")]))
  matches .ok (.number "a" none none)
#guard (decodeBinder (Json.mkObj [("name", "x"), ("kind", "real")])) matches .error _
-- A bound is an op × literal pair; a bare string is not one.
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"), ("lower", "0")]))
  matches .error _

-- Guards are optional, decode in order, and name their own field when
-- they break the schema.
def payloadShell (guards : Json) : Json :=
  Json.mkObj
    [("kind", "structured"), ("binders", Json.arr #[]), ("guards", guards),
     ("conclusion", Json.mkObj
       [("kind", "istrue"), ("expr", Json.mkObj [("kind", "id"), ("name", "b")])])]

#guard
  (decodePayload (payloadShell (Json.arr
    #[Json.mkObj [("kind", "id"), ("name", "g")],
      Json.mkObj [("kind", "id"), ("name", "h")]])))
  matches .ok (.structured #[] #[.id "g", .id "h"] (.istrue (.id "b")))
#guard (decodePayload (payloadShell "g")) matches .error "field 'guards' is not an array"
#guard
  (decodePayload (payloadShell (Json.arr #[Json.mkObj [("kind", "cond")]])))
  matches .error "field 'guards': unknown expression kind 'cond'"

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

#eval goldenCheck "tests/fixtures/statements.emission.json"
  "tests/fixtures/statements.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/binders.emission.json"
  "tests/fixtures/binders.emitted.lean.expected"

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
                       payload := .structured #[.int "bump"] #[]
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
                       payload := .structured #[.int "pure"] #[]
                         (.istrue (.binop ">=" (.call "f" #[.id "pure"])
                                             (.num "0"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "pure'").length == 3 do
    throwError "the reserved binder name is not primed:\n{rendered}"

-- The statement decoding round-trips strictly, else arm optional.
#guard
  (decodeStmt (Json.mkObj [("kind", "throw"), ("error", "RangeError")]))
  matches .ok (.throwErr "RangeError")
#guard
  (decodeStmt (Json.mkObj
    [("kind", "let"), ("name", "y"),
     ("init", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.letDecl "y" (.id "x"))
#guard
  (decodeStmt (Json.mkObj
    [("kind", "if"),
     ("cond", Json.mkObj [("kind", "id"), ("name", "b")]),
     ("then", Json.arr #[Json.mkObj [("kind", "throw"), ("error", "E")]])]))
  matches .ok (.ite (.id "b") #[.throwErr "E"] none)
#guard (decodeStmt (Json.mkObj [("kind", "while")])) matches .error _

-- A mutable local renders as `let mut`, a reassigned parameter is rebound
-- ahead of the body, and no join helper reaches the source text.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "clampUp", params := #["x"], source := "clampUp",
                        body := #[
                          .ite (.binop "<" (.id "x") (.num "1"))
                            #[.assign "x" (.num "1")] none,
                          .ret (.id "x")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "let mut x := x").length == 2 do
    throwError "the assigned parameter is not rebound:\n{rendered}"
  unless (rendered.splitOn "fun").length == 1 do
    throwError "a helper lambda leaked into the source text:\n{rendered}"

-- A number binder is a Float ∀ carrying its bounds as hypotheses, lower
-- outermost, with an infinite endpoint spelled `floatInf` — and no use of
-- it is coerced, since it is already a double. The wide conclusion also
-- pins the join: `return` never ends a line, which would read back as a
-- bare return.
#eval show CoreM Unit from do
  let call (x : String) : JsExpr :=
    .call "applyConversionFactors" #[.id x, .id x, .id x, .id x, .id x]
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "applyConversionFactors",
                        params := #["v", "sf", "so", "tf", "to"],
                        source := "applyConversionFactors",
                        body := #[.ret (.id "v")] }]
    obligations := #[{ function := "applyConversionFactors", property := "p",
                       formula := "f",
                       payload := .structured
                         #[.number "x" (some ("<", "0")) (some ("<", "Infinity")),
                           .number "y" (some ("<=", "-Infinity")) none]
                         #[] (.istrue (.binop "<=" (call "x") (call "y"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "∀ (x : JsNumber),").length == 2 do
    throwError "the number binder is not a JsNumber ∀:\n{rendered}"
  -- The printer breaks after every arrow, so order is pinned by nesting:
  -- the upper bound must sit inside the lower.
  let underLower := rendered.splitOn "0 < x →"
  unless underLower.length == 2 do
    throwError "the lower bound did not render:\n{rendered}"
  unless ((underLower[1]!).splitOn "x < floatInf →").length == 2 do
    throwError "the upper bound is not inside the lower:\n{rendered}"
  unless (rendered.splitOn "-floatInf ≤ y →").length == 2 do
    throwError "the half-bounded number binder did not render:\n{rendered}"
  unless (rendered.splitOn "Float.ofInt").length == 1 do
    throwError "a number binder was coerced from Int:\n{rendered}"
  unless (rendered.splitOn "return\n").length == 1 do
    throwError "a return was split from its argument:\n{rendered}"
  -- The positive half of the same pin: the conclusion is wide enough that
  -- the printer breaks it, so this is the rejoined line, not an unbroken one.
  unless (rendered.splitOn "return Float.le").length == 2 do
    throwError "the return and its argument are not on one line:\n{rendered}"

-- A shape outside the slice is refused with a message naming the gap.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[{ name := "helper.mts::double", params := #["x"],
                        source := "f", body := #[.ret (.id "x")] }]
    obligations := #[] }
  let refused ← try
    let _ ← renderEmission e
    pure false
  catch _ => pure true
  unless refused do
    throwError "a module-qualified name was rendered instead of refused"
