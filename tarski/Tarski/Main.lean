import Tarski.Decode
import Tarski.Eval
import Tarski.Format

/-! The `tarski` binary: `tarski run <file.json>`.

One ESTree document in — the JSON `schemas/tarski-estree.schema.json`
fixes, as the parser bridge produces it — one line out: the script's
completion value, or nothing when no statement produced one.

Exit codes:

* `0` — the script ran. Its completion value, if any, is on stdout.
* `1` — the script ended with an uncaught abrupt completion. `uncaught:`
  and the thrown value are on stderr.
* `2` — the input is not a script this binary can be handed: bad usage,
  an unreadable file, text that is not JSON, or a document outside the
  schema. The reason is on stderr.
* `3` — the script contains a node the evaluator does not know.
  `unsupported:` and the node kind are on stderr.

Divergence is not an exit code. A program that does not terminate is a
run this binary never returns from; the caller imposes a timeout and
reads the answer from that. -/

open Lean Tarski

/-- Run one decoded program and report it. -/
def report (program : Program) : IO UInt32 :=
  match runProgram program with
  | some (.ok none) => pure 0
  | some (.ok (some v)) => do
    IO.println (formatValue v)
    pure 0
  | some (.error (.throw v)) => do
    IO.eprintln s!"uncaught: {formatValue v}"
    pure 1
  | some (.error _) => do
    -- No node in this slice builds a `break`, `continue`, or `return`.
    IO.eprintln "uncaught: abrupt completion outside any loop or function"
    pure 1
  | none => do
    -- The logical model of divergence. Compiled code loops instead of
    -- answering `none`, so nothing reaches this.
    IO.eprintln "tarski: evaluation produced no result"
    pure 2

def run (path : String) : IO UInt32 := do
  let text ←
    try
      IO.FS.readFile path
    catch e =>
      IO.eprintln s!"tarski: {e}"
      return 2
  match Json.parse text with
  | .error msg =>
    IO.eprintln s!"tarski: {path}: {msg}"
    return 2
  | .ok json =>
    match decodeProgram json with
    | .error e@(.unsupported _) =>
      IO.eprintln e.message
      return 3
    | .error e@(.malformed _) =>
      IO.eprintln s!"tarski: {path}: {e.message}"
      return 2
    | .ok program => report program

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", path] => run path
  | _ =>
    IO.eprintln "usage: tarski run <file.json>"
    return 2
