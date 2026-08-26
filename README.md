# Lakatos

Proofs and refutations for TypeScript.

You state a property of a function in a JSDoc annotation. Lakatos tries to
**refute** it — thousands of generated inputs hunting for a counterexample —
and then tries to **prove** it, for all inputs, with a theorem prover. You
get the strongest verdict your property has earned:

```
$ lakatos check src/foo.ts
foo # nonzero      REFUTED    counterexample: x = -1n, y = 0
bar # involutive   PROVED
baz # monotone     TESTED     10,000 runs, no counterexample; not proved
```

The name is from Imre Lakatos's _Proofs and Refutations_: mathematics
advances by conjectures, attempted proofs, and counterexamples that force
the conjecture to be repaired. That loop is exactly what this tool runs.

## Status

Both engines work end to end. `lakatos refute` scrapes `@ensures`
annotations, generates fast-check property tests, runs them, and prints a
per-annotation JSON report. `lakatos prove` emits a `.lean`
artifact per file under the run directory, runs it through the Lean engine
(`lake env lean`), and assembles the same per-annotation envelope from the
prover's verdicts; it requires the Lean toolchain (elan/lake) on PATH and,
for now, a lakatos checkout — the npm package does not yet ship the Lean
engine. `lakatos check` is a stub: it scrapes the same annotations,
reports each one `NotTried`, and exits 1. The rest of this README
describes the committed design.

Every invocation writes its artifacts into its own directory under
`.lakatos/`, named for the run's start time in UTC — the same instant the
report carries as `startedAt`. Nothing is ever overwritten and nothing is
ever pruned: add `.lakatos/` to your `.gitignore` and delete it when you
want the space back.

## Usage

```
$ lakatos refute src/foo.ts
lakatos: generated 1 property across 1 file(s) into .lakatos/2026-08-17T12-53-06.896Z/pabst/
{
  "version": "0.1.0",
  "startedAt": "2026-08-17T12:53:06.896Z",
  "cwd": "/path/to/project",
  "seed": 4226542574,
  "generated": 1,
  "passed": 0,
  "failed": 1,
  "annotations": [
    {
      "file": "src/foo.ts",
      "function": "isZero",
      "property": "wrong",
      "szs": "CounterSatisfiable",
      "kind": "falsified",
      "counterexample": {
        "x": 1
      }
    }
  ]
}
$ echo $?
1
```

The report (schema: `schemas/envelope.schema.json`) lists every scraped
annotation with an [SZS ontology](https://tptp.org/UserDocs/SZSOntology/)
status:

| Outcome                                 | SZS status           |
| --------------------------------------- | -------------------- |
| proved for all inputs                   | `Theorem`            |
| falsified (counterexample)              | `CounterSatisfiable` |
| property body threw / prover errored    | `Error`              |
| generation exhausted / passed / gave up | `GaveUp`             |
| annotation depends on unmappable code   | `Inappropriate`      |
| not attempted (stubs, unhealthy runs)   | `NotTried`           |
| malformed annotation input              | `InputError`         |
| run interrupted before evaluating it    | `User`               |

The two `GaveUp` cases are distinguished by the `kind` field: present
(`"exhausted"`) when generation gave up, absent when every run passed.

`NotTried` also covers unhealthy runs: when the underlying engine run
fails outright — the test runner dies before reporting, a generated test
can't even load, the Lean toolchain is missing, the Lean run fails, or
its verdict lines are malformed — no property was actually evaluated, so
the run reports every scraped annotation `NotTried`, keeps the
diagnostics on stderr, and exits 2. Stdout is one parseable envelope in
every mode.

`User` covers interrupted runs: Ctrl-C at the terminal, a supervisor's
SIGTERM, a CI cancel. The run stops, every annotation it had not
finished evaluating reports `User` with the signal in its `reason`,
annotations already resolved keep the status they earned, and the run
exits 2. This holds for a signal that arrives while an engine is running
— the vitest of a refute, the lake or Lean of a prove — which is where a
run spends nearly all of its time. Outside that window, and for SIGKILL
anywhere, lakatos dies as any process does and prints nothing: not a
contract lakatos can keep, so it does not claim to.

`InputError` marks an annotation whose input is malformed at extraction
— a duplicate property name (all claimants of the ambiguous identity
collapse into one entry), or an `@ensures` on an inaccessible subject
such as a non-exported class or a non-public member. Sound annotations
in the same run still get real verdicts; the entry's `error` field
carries the diagnostic, and the run exits 2. Subjects without a proper
name still get entries under best-effort labels (`<anonymous>#m`,
`Box#<computed>`), with the diagnostic saying what is unsupported.

Commands: `lakatos refute` and `lakatos prove` (work today),
`lakatos check` (stub). All take `[files-or-globs...]`; with no files,
sources are discovered via `tsconfig.json` or `src/**`. `--seed <n>`
applies to refute only: passing a report's `seed` back reproduces its
run.

Exit codes: `0` — clean run; `1` — counterexamples found, or a stubbed
command; `2` — usage or user error, including an unhealthy or
interrupted run.

## Layout

Everything is one repository, one product, one version number:

- `src/` — the lakatos CLI frontend (the npm package at the repo root).
- [`engines/thales/`](engines/thales/) — the proof engine: a
  TypeScript-to-Lean 4 compiler with a graded automatic discharge ladder
  (exhaustive checking on bounded domains, then a fixed tactic stack, then
  an honest "unable to prove").
- [`engines/pabst/`](engines/pabst/) — the refutation engine: compiles
  properties to [fast-check](https://fast-check.dev/) runs.
- [`spec/`](spec/) — the Lemma annotation language: grammar, prose
  semantics, and conformance fixtures.

## Architecture

Lakatos is a thin frontend over two engines, one per side of the dialectic:

```
                 lakatos  (CLI, npm)
                /        \
        refute /          \ prove
              v            v
        engines/pabst   engines/thales
        (TypeScript;    (Lean 4; prebuilt per-platform
         fast-check)     bundle, auto-downloaded on
                         first use)
```

The engines never depend on each other. Neither requires you to install
Lean: the Lean engine ships as a prebuilt per-platform bundle that lakatos
fetches once, Playwright-style. The bundle is built from this repository's
own releases — frontend and engine are cut from the same commit, so there
is no engine version to pin and no skew to manage.

Properties are written in [Lemma](spec/), a little specification language
embedded in JSDoc — annotated files remain ordinary TypeScript accepted by
`tsc --strict`.

## Commands

- **`lakatos check <file>`** — the flagship: refute first (fast — catches
  false properties in seconds), then prove, then report one graded verdict
  per property.
- `lakatos prove <file>` — proof engine only.
- `lakatos refute <file>` — refutation engine only. Note the semantics:
  the command names the _attempt_; finding no counterexample is success
  (exit 0), like any test run.

## Verdicts

This section is the committed design for `lakatos check`, which is still
a stub; today the JSON report shown under Usage is the only output.
Human-readable verdicts lead; each carries an
[SZS ontology](https://tptp.org/UserDocs/SZSOntology/) status as
metadata, shared with both engines' own output:

| Verdict            | SZS status           | Meaning                                                                                                                                           |
| ------------------ | -------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| PROVED             | `Theorem`            | Holds for all inputs. Any assumptions (opaque callees, assumed contracts) are listed with the verdict — the trust boundary is impossible to miss. |
| REFUTED            | `CounterSatisfiable` | A concrete counterexample was found and is reported.                                                                                              |
| TESTED, not proved | `Unknown`            | The refuter found nothing in its budget and the prover gave up; per-engine sub-statuses (`GaveUp`, `Timeout`) say why.                            |

Exit codes are deliberately boring: `0` — no property refuted; `1` — at
least one property refuted (or a counterexample found by the prover);
`2` — input or usage error. "Tested but not proved" exits `0` with a
diagnostic: an unproved truth is not a failure.

## License

MIT.
