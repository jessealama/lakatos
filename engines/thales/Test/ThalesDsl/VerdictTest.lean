import ThalesDsl.Verdict

open ThalesDsl

def sample (cex : Option (Array (String × Int))) : Verdict :=
  { identity := ⟨"f.ts", "fn", "prop"⟩
    szs := "CounterSatisfiable"
    reason := "false on its bounded domain"
    counterexample := cex }

-- Without a counterexample the wire shape is unchanged.
#guard (sample none).toJson.compress
  = "{\"identity\":[\"f.ts\",\"fn\",\"prop\"],\"reason\":\"false on its bounded domain\",\"szs\":\"CounterSatisfiable\"}"

-- A counterexample rides along as an object (mkObj emits keys sorted).
#guard (sample (some #[("x", 3), ("y", -2)])).toJson.compress
  = "{\"counterexample\":{\"x\":3,\"y\":-2},\"identity\":[\"f.ts\",\"fn\",\"prop\"],\"reason\":\"false on its bounded domain\",\"szs\":\"CounterSatisfiable\"}"

-- Values outside the JS safe-integer range travel as decimal strings so
-- JSON.parse on the CLI side cannot lose precision.
#guard (sample (some #[("x", 9007199254740991), ("y", 9007199254740992)])).toJson.compress
  = "{\"counterexample\":{\"x\":9007199254740991,\"y\":\"9007199254740992\"},\"identity\":[\"f.ts\",\"fn\",\"prop\"],\"reason\":\"false on its bounded domain\",\"szs\":\"CounterSatisfiable\"}"

#guard (sample (some #[("x", -9007199254740991), ("y", -9007199254740992)])).toJson.compress
  = "{\"counterexample\":{\"x\":-9007199254740991,\"y\":\"-9007199254740992\"},\"identity\":[\"f.ts\",\"fn\",\"prop\"],\"reason\":\"false on its bounded domain\",\"szs\":\"CounterSatisfiable\"}"
