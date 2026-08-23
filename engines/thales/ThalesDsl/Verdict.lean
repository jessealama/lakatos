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

/-- One per-annotation result, printed as a single JSON line on stdout.
This is the contract between `#thales_prove` and the lakatos CLI. -/
structure Verdict where
  identity : Identity
  szs : Szs
  reason : String
  /-- Binder-name/value pairs falsifying the property, in binder order. -/
  counterexample : Option (Array (String × Int)) := none
  /-- Theorem only: the non-standard axioms the proof depends on, read off
  the theorem itself. Empty for a kernel-checked proof. -/
  axioms : Option (Array Lean.Name) := none

/-- Values outside the JS safe-integer range travel as decimal strings so
`JSON.parse` on the CLI side cannot lose precision. -/
def Verdict.jsonInt (v : Int) : Lean.Json :=
  if v.natAbs ≤ 9007199254740991 then .num v else .str (toString v)

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
      [("counterexample", Lean.Json.mkObj (cex.toList.map fun (n, x) => (n, jsonInt x)))]) ++
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

end ThalesDsl
