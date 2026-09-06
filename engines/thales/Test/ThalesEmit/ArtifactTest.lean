import Test.ThalesEmit.Support

/-! The printed artifact: five goldens a person inspected and accepted,
one per artifact shape, and the pins that are about text rather than
trees. Paths are relative to engines/thales, where every lake invocation
runs. -/

open Lean ThalesEmit

def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

-- #eval runs CoreM inside this module's own environment, which imports
-- ThalesDsl transitively, so the printer has its syntax tables.
def goldenCheck (emissionPath expectedPath : String) : CoreM Unit := do
  let text ← IO.FS.readFile emissionPath
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let rendered ← renderEmission e
  let expected ← IO.FS.readFile expectedPath
  unless rendered == expected do
    throwError "rendered artifact drifted from the golden file:\n{rendered}"

/-- A fixture whose rules are pinned as syntax guards: it must still
render, and (once the emitter checks it) round-trip, but its text is not a
golden. -/
def rendersOk (emissionPath : String) : CoreM Unit := do
  let text ← IO.FS.readFile emissionPath
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let _ ← renderEmission e

#eval goldenCheck "tests/fixtures/tracer.emission.json"
  "tests/fixtures/tracer.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/statements.emission.json"
  "tests/fixtures/statements.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/classes.emission.json"
  "tests/fixtures/classes.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/unions.emission.json"
  "tests/fixtures/unions.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/optionals.emission.json"
  "tests/fixtures/optionals.emitted.lean.expected"

#eval rendersOk "tests/fixtures/operators.emission.json"
#eval rendersOk "tests/fixtures/binders.emission.json"
#eval rendersOk "tests/fixtures/degradations.emission.json"
#eval rendersOk "tests/fixtures/class-params.emission.json"
#eval rendersOk "tests/fixtures/class-binder-equality-guards.emission.json"
#eval rendersOk "tests/fixtures/nested-class-binder.emission.json"
#eval rendersOk "tests/fixtures/module-consts.emission.json"
#eval rendersOk "tests/fixtures/defaults.emission.json"
#eval rendersOk "tests/fixtures/ctor-defaults.emission.json"
#eval rendersOk "tests/fixtures/instance-defaults.emission.json"
#eval rendersOk "tests/fixtures/object-is-tagged.emission.json"

-- A dependency's constant sits one component deeper, like its functions.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[
      .const { name := "cap", module := some "constants.mts",
               lit := "-0.5", source := "export const cap = -0.5;" }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.«constants.mts».cap : JsNumber :=").length == 2 do
    throwError "the dependency constant is not module-qualified:\n{rendered}"
  -- Once in the source echo, once as the def's value.
  unless (rendered.splitOn "-0.5").length == 3 do
    throwError "the negated literal did not render:\n{rendered}"

-- A dependency's block is introduced once, ahead of its def; the entry's
-- declarations get no separator of their own.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "main.mts"
    declarations := #[
      .fn { name := "double", module := some "helper.mts", params := nums #["x"],
            source := "double", body := #[.ret (.binop "*" (.id "x") (.num "2"))] },
      .fn { name := "twice", params := nums #["x"], source := "twice",
            body := #[.ret (.call "double" (some "helper.mts") #[.id "x"])] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "-- module helper.mts\n").length == 2 do
    throwError "the module separator is missing or repeated:\n{rendered}"
  let afterSep := (rendered.splitOn "-- module helper.mts\n")[1]!
  unless (afterSep.splitOn "def TsModel.«helper.mts».double").length == 2 do
    throwError "the module separator does not precede its def:\n{rendered}"
  unless (rendered.splitOn "-- module ").length == 2 do
    throwError "the entry's declarations got a separator:\n{rendered}"

-- The wide conclusion pins the join: `return` never ends a line, which
-- would read back as a bare return.
#eval show CoreM Unit from do
  let call (x : String) : JsExpr :=
    .call "applyConversionFactors" none #[.id x, .id x, .id x, .id x, .id x]
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "applyConversionFactors",
                            params := nums #["v", "sf", "so", "tf", "to"],
                            source := "applyConversionFactors",
                            body := #[.ret (.id "v")] }]
    obligations := #[{ function := "applyConversionFactors", property := "p",
                       formula := "f",
                       payload := .structured
                         #[.number "x" (some (.lt, "0")) (some (.lt, "Infinity")),
                           .number "y" (some (.le, "-Infinity")) none]
                         #[] (.istrue (.binop "<=" (call "x") (call "y"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "return\n").length == 1 do
    throwError "a return was split from its argument:\n{rendered}"
  -- The positive half of the same pin: the conclusion is wide enough that
  -- the printer breaks it, so this is the rejoined line, not an unbroken one.
  unless (rendered.splitOn "return Float.le").length == 2 do
    throwError "the return and its argument are not on one line:\n{rendered}"
