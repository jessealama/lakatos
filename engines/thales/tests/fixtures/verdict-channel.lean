import ThalesDsl

-- Two healthy stub commands: each must yield exactly one verdict line.
#thales_prove "add.ts" "add" "forall (a b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }"
#thales_prove "add.ts" "sub" "forall (a: int ∈ [0, 10)) { sub(a, a) ≡ 0 }"

-- Deliberate elaboration failure: the ill-typed term must be contained to
-- this command's verdict line and must not abort the file.
#thales_prove "add.ts" "bad" "forall (a: int ∈ [0, 10)) { bad(a) ≡ 0 }" := (fun (x : Nat) => x) "two"

-- A command after the failure proves later commands still report.
#thales_prove "add.ts" "tail" "forall (a: int ∈ [0, 10)) { tail(a) ≡ a }"
