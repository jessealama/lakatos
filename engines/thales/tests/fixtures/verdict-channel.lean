import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- Two healthy stub commands (no structured property yet): each must yield
-- exactly one NotTried verdict line.
#thales_prove "add.ts" "add" "commutes"
#thales_prove "add.ts" "sub" "cancels"

-- Deliberate elaboration failure: the payload is ill-typed. The failure
-- must be contained to this command's verdict line and must not abort the
-- file.
#thales_prove "add.ts" "bad" "illTyped" := Nat.succ "x"

-- A command after the failure proves later commands still report.
#thales_prove "add.ts" "tail" "reports"
