# Verdict-fixture corpus

End-to-end fixtures for `lakatos prove`. Each `.ts` file is one fixture, and
its directory is its entire test specification: every `@ensures` annotation
in the file must receive the bucket's SZS status. There are no sidecar files
and no inline expectation directives.

The harness is the root `tests/verdict-corpus.test.ts`, gated on
`LAKATOS_PROVE_E2E=1` like the prove e2e (it needs the Lean toolchain and is
minutes-slow). It copies the corpus into a scratch project, runs
`lakatos prove` once over every fixture, and diffs each annotation's status
against its bucket. Only the SZS status is bucket-checked; reason text is
the business of the e2e and unit suites.

## Buckets

- `theorem/` — every annotation proves (`Theorem`).
- `countersatisfiable/` — a false bounded claim: decide establishes falsity
  and the prover extracts a concrete witness (`CounterSatisfiable`).
- `gaveup/` — the proof ladder exhausts (`GaveUp`): an unbounded claim, for
  which there is no finite domain to evaluate and no arithmetic theory to
  reason with, so falsity on an unbounded domain has no counterexample to
  ship either. Also a bounded claim shown false whose witness the prover
  could not read back, which ships the falsity without the illustration.
- `nottried/` — the transcriber degrades the property (`NotTried`): it has
  no structured reading (a half-bounded range the DSL has no binder shape
  for, a connective other than a top-level implication chain of atoms), or
  a range endpoint exceeds the safe integer range.
- `inappropriate/` — the annotation is outside the model: the function uses
  a construct the transcriber cannot map, or an operator the model refuses
  on the merits (`Inappropriate`).
- `timeout/` — every annotation must report `Timeout` under the reduced
  heartbeat budget the harness sets via `LAKATOS_PROVE_HEARTBEATS`; the
  bucket runs as its own prove invocation so the rest of the corpus keeps
  the default budget.

Buckets are named after SZS statuses, lowercase. Buckets for statuses the
prover cannot yet reach arrive with the issues that add those capabilities,
so a capability upgrade shows up in the diff as a `git mv` between buckets
(the refuting prover moved false-claim fixtures from `gaveup/` to
`countersatisfiable/` exactly this way).

## Adding a fixture

Author a `.ts` file with at least one `@ensures` annotation, run the harness
locally, and place the file by its observed-and-intended verdict:

    LAKATOS_PROVE_E2E=1 npx vitest run tests/verdict-corpus.test.ts

A surprising verdict at authoring time is a finding to resolve, not an
expectation to adjust silently. If a file's annotations would earn different
verdicts, split it into one file per bucket.
