import Lean.Data.Json

namespace ThalesDsl

/-- The per-annotation identity key shared with the refutation engine:
`[file, function, property]`. -/
structure Identity where
  file : String
  function : String
  property : String

/-- The SZS statuses a verdict can carry, closed so a status cannot be
invented or misspelled at an emission site. The CLI's `ProveStatus`
(root `src/szs.ts`) enumerates exactly these; the root suite pins the two. -/
inductive Szs where
  | Theorem
  | CounterSatisfiable
  | Inappropriate
  | GaveUp
  | Timeout
  | NotTried
  | Error
  deriving DecidableEq

/-- The wire spelling: each constructor's own name. -/
def Szs.toString : Szs → String
  | .Theorem => "Theorem"
  | .CounterSatisfiable => "CounterSatisfiable"
  | .Inappropriate => "Inappropriate"
  | .GaveUp => "GaveUp"
  | .Timeout => "Timeout"
  | .NotTried => "NotTried"
  | .Error => "Error"

/-- One binder's value in a witness: an integer from an enumerated range,
or a boolean from a boolean binder. -/
inductive WitnessValue where
  | int (i : Int)
  | bool (b : Bool)
  deriving Repr, BEq, DecidableEq

/-- One per-annotation result, printed as a single JSON line on stdout.
This is the contract between `#thales_prove` and the lakatos CLI. -/
structure Verdict where
  identity : Identity
  szs : Szs
  reason : String
  /-- Binder-name/value pairs falsifying the property, in binder order. -/
  counterexample : Option (Array (String × WitnessValue)) := none
  /-- Theorem only: the non-standard axioms the proof depends on, read off
  the theorem itself. Empty for a kernel-checked proof. -/
  axioms : Option (Array Lean.Name) := none

/-- Values outside the JS safe-integer range travel as decimal strings so
`JSON.parse` on the CLI side cannot lose precision. -/
def Verdict.jsonInt (v : Int) : Lean.Json :=
  if v.natAbs ≤ 9007199254740991 then .num v else .str (toString v)

/-- A witness value on the wire: an integer under the safe-integer rule,
a boolean as a JSON boolean. -/
def WitnessValue.toJson : WitnessValue → Lean.Json
  | .int i => Verdict.jsonInt i
  | .bool b => .bool b

def Verdict.toJson (v : Verdict) : Lean.Json :=
  Lean.Json.mkObj <|
    [
      ("identity", Lean.Json.arr #[.str v.identity.file, .str v.identity.function, .str v.identity.property]),
      ("szs", .str v.szs.toString),
      ("reason", .str v.reason)
    ] ++
    (match v.counterexample with
    | none => []
    | some cex =>
      [("counterexample", Lean.Json.mkObj (cex.toList.map fun (n, x) => (n, x.toJson)))]) ++
    match v.axioms with
    | none => []
    | some axs =>
      [("axioms", Lean.Json.arr (axs.map fun a => .str a.toString))]

/-- Frames each verdict line: stdout is also Lean's diagnostic stream, and
the CLI treats only framed lines as part of the contract. -/
def Verdict.sentinel : String := "thales-verdict:"

/-- Verdicts must be one line each: `Json.compress` never emits newlines. -/
def Verdict.emit (v : Verdict) : IO Unit :=
  IO.println (Verdict.sentinel ++ v.toJson.compress)

/-! ## The model channel

The second sentinel. A verdict says what was proved about a declaration's
*model*; a model line says whether that model is the declaration — whether
the evaluator's run of the declaration's own AST, projected, equals it.
The two are independent: an unvalidated model never changes a verdict
(the design record's D7), it only marks how far the verdict's trust
reaches. -/

/-- Whether a declaration's model was proved equal to its evaluator run. -/
inductive ModelStatus where
  | validated
  | unvalidated
  deriving DecidableEq

/-- The wire spelling: each constructor's own name, lowercased as the
statuses are written in the envelope. -/
def ModelStatus.toString : ModelStatus → String
  | .validated => "validated"
  | .unvalidated => "unvalidated"

/-- One `#thales_validate` result, printed as a single JSON line on
stdout. This is the trust marker D7 defines, one per validated
declaration rather than one per annotation: `run.ts` joins it onto every
annotation of that function. `reason` is present exactly when the status
is `unvalidated`. -/
structure ModelLine where
  file : String
  /-- The declaration's plain name, the spelling a verdict's identity
  carries in its second position. -/
  function : String
  status : ModelStatus
  reason : Option String := none

/-- A declaration whose model is the evaluator's run of its own AST. -/
def ModelLine.validated (file fn : String) : ModelLine :=
  ⟨file, fn, .validated, none⟩

/-- A declaration whose model was not established. An empty reason is a
contract violation on the CLI side — and a contract violation fails the
whole artifact — so an empty one is replaced rather than shipped. -/
def ModelLine.unvalidated (file fn reason : String) : ModelLine :=
  ⟨file, fn, .unvalidated, some (if reason.isEmpty then "no reason given" else reason)⟩

def ModelLine.toJson (m : ModelLine) : Lean.Json :=
  Lean.Json.mkObj <|
    [
      ("file", .str m.file),
      ("function", .str m.function),
      ("status", .str m.status.toString)
    ] ++
    match m.reason with
    | none => []
    | some r => [("reason", .str r)]

/-- Frames each model line, beside `Verdict.sentinel` on the same stream.
`run.ts` reads both. -/
def ModelLine.sentinel : String := "thales-model:"

/-- Model lines must be one line each: `Json.compress` never emits
newlines. -/
def ModelLine.emit (m : ModelLine) : IO Unit :=
  IO.println (ModelLine.sentinel ++ m.toJson.compress)

end ThalesDsl
