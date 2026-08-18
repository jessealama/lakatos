import Lean.Data.Json

namespace ThalesDsl

/-- The per-annotation identity key shared with the refutation engine:
`[file, function, property]`. -/
structure Identity where
  file : String
  function : String
  property : String

/-- One per-annotation result, printed as a single JSON line on stdout.
This is the contract between `#thales_prove` and the lakatos CLI. -/
structure Verdict where
  identity : Identity
  szs : String
  reason : String

def Verdict.toJson (v : Verdict) : Lean.Json :=
  Lean.Json.mkObj [
    ("identity", Lean.Json.arr #[.str v.identity.file, .str v.identity.function, .str v.identity.property]),
    ("szs", .str v.szs),
    ("reason", .str v.reason)
  ]

/-- Frames each verdict line: stdout is also Lean's diagnostic stream, and
the CLI treats only framed lines as part of the contract. -/
def Verdict.sentinel : String := "thales-verdict:"

/-- Verdicts must be one line each: `Json.compress` never emits newlines. -/
def Verdict.emit (v : Verdict) : IO Unit :=
  IO.println (Verdict.sentinel ++ v.toJson.compress)

end ThalesDsl
