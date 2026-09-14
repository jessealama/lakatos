import Tarski.Decode
import Tarski.Eval
import Tarski.Format

/-! The `tarski` binary: `tarski run <file.json>` and
`tarski exec <file.json>`.

One ESTree document in — the JSON `schemas/tarski-estree.schema.json`
fixes, as the parser bridge produces it — one line out: the script's
completion value, or nothing when no statement produced one.

`exec` is what `lakatos exe` calls, and its one difference from `run` is
that it prints **no** completion value: a program run for its effects
answers nothing a user asked for, and `node file.js` prints none either.
Everything else — the print log, the uncaught report, the exit codes — is
`run`'s exactly.

Exit codes:

* `0` — the script ran. Under `run`, its completion value, if any, is
  on stdout; under `exec` there is no such line.
* `1` — the script ended with an uncaught abrupt completion. `Uncaught `
  and the thrown value are on stderr: `<name>: <message>` for an Error
  object, the value's printed form otherwise.
* `2` — the input is not a script this binary can be handed: bad usage,
  an unreadable file, text that is not JSON, or a document outside the
  schema. The reason is on stderr.
* `3` — the script contains a node the evaluator does not know.
  `unsupported:` and the node kind are on stderr.

What the host's `print` was given is on stdout, one line per call, ahead
of the completion value and ahead of any report on stderr. The lines are
accumulated in the heap during the run (see `%PrintLog%` in
`Tarski/Realm.lean`) and written out once, so a run that ends abruptly
still shows what it printed before it did.

Divergence is not an exit code. A program that does not terminate is a
run this binary never returns from; the caller imposes a timeout and
reads the answer from that. -/

open Lean Tarski

/-- Write out what `print` was given during the run, one line each. -/
def printLog (h : Heap) : IO Unit :=
  h.printedLines.forM IO.println

/-- Run one decoded program and report it. `printCompletion` is the one
difference between `run` (`true`) and `exec` (`false`). -/
def report (printCompletion : Bool) (program : Program) : IO UInt32 :=
  match runScript program with
  | some (.ok none, h) => do
    printLog h
    pure 0
  | some (.ok (some v), h) => do
    printLog h
    if printCompletion then IO.println (formatValue v)
    pure 0
  | some (.error (.throw v), h) => do
    -- The heap the throw came out with is where the thrown object is, so
    -- the report is computed in it.
    printLog h
    IO.eprintln s!"Uncaught {describeThrown h v}"
    pure 1
  | some (.error _, h) => do
    printLog h
    -- A `return` outside any function, a `break` or `continue` outside
    -- any loop, or a jump to a label that is not on the stack. An engine
    -- refuses each as an early error, and early errors are outside the
    -- epic, so they are reported here as the abrupt completions they are.
    IO.eprintln "Uncaught: abrupt completion outside any loop, label, or function"
    pure 1
  | none => do
    -- The logical model of divergence. Compiled code loops instead of
    -- answering `none`, so nothing reaches this.
    IO.eprintln "tarski: evaluation produced no result"
    pure 2

/-- The body both subcommands share: read, parse, decode, report. -/
def execute (printCompletion : Bool) (path : String) : IO UInt32 := do
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
    | .ok program => report printCompletion program

/-- `tarski run`: the completion value is a line of output. -/
def run (path : String) : IO UInt32 := execute true path

/-- `tarski exec`: it is not. -/
def exec (path : String) : IO UInt32 := execute false path

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", path] => run path
  | ["exec", path] => exec path
  | _ =>
    IO.eprintln "usage: tarski run|exec <file.json>"
    return 2
