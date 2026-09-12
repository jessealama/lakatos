# CLAUDE.md

Pabst is lakatos's refutation engine: `@ensures` annotations become fast-check property tests, generated into the target project's per-run directory and executed with vitest; failures come back as per-annotation issues the CLI maps to SZS statuses (`falsified` → CounterSatisfiable, `threw` → Error, `exhausted` → GaveUp, `budget` → Timeout).

Root-package code: no toolchain, lockfile, or package of its own. Build, test, and typecheck from the repo root; only its library tests live here (`tests/`). Annotation parsing is not here: pabst consumes lemma's parsed `Binder`/`Formula` and owns only what is fast-check-specific.

## Where to start

- `src/build-spec.ts` — lemma's output → one flat `PropertySpec` per annotation (`src/ir.ts`); `src/lower.ts` (`lowerTop`) flattens the formula to JS boolean text.
- `src/codegen.ts` + `src/emit.ts` — string-build one vitest file per source file; `src/enumerate.ts` picks exhaustive enumeration vs sampling; `src/domains.ts` renders arbitraries from lemma's bounds.
- `src/run.ts` — runs lakatos's own vitest under the current node (no npx) and classifies the outcome.
- `src/contract.ts` — every string that must agree across emitted test ↔ `src/runtime.ts` ↔ CLI decoder. `tests/contract-pins.test.ts` names every other spelling to update when one changes.

## What the code can't tell you

- Generated tests import from `lakatos/runtime`, the root package's only export subpath, resolved from the _target project's_ node_modules — which is why refute must run from that project.
- Domains lemma cannot represent (an interval endpoint beyond the safe-integer range) yield no spec at all and report `NotTried` / `unsupported-range`, exactly as prove does: generating over a clamped domain would refute a narrower statement than the one written. The classification is lemma's (`clampedEndpoints`, `unsupportedRangeReason`), so the engines cannot diverge on it.
- A spec over at most 1,000 tuples (`ENUMERATION_CAP`) is walked in full and a clean pass is a Theorem the CLI marks `enumerated`; each enumerated test has a 4 s wall-clock budget (`LOOP_BUDGET_MS`), the source of the `budget` kind. Sampled specs run 1,000 cases (`SAMPLE_RUNS`) under a random 32-bit seed per run, reproducible with `--seed`.
- Run outcomes are `completed`, `no-results`, `broken-run`, and `interrupted`; an interrupted run is the CLI's `User` status, never an error.

## Conventions

- **Generated code is disposable.** Every run writes a fresh directory; determinism comes from the seed.
- **Engine-neutral logic goes to `lemma/`; fast-check-specific logic stays here.** `domains.ts` must not re-derive bounds arithmetic.
- **Input faults throw `LemmaError`** (exit 2 with a one-line diagnostic); anything else escaping is an internal bug. An unrepresentable domain is not the input's fault: contained per annotation, never a run-level abort.
- **Never depend on thales**, and vice versa; sharing goes through `lemma/` and the root contract.

Stryker (`npm run mutation`, root config) targets pabst's sources but runs locally only; CI runs the vitest suite.
