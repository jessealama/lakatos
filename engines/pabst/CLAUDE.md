# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working on the pabst engine.

## What this engine is

Pabst is lakatos's refutation engine. It backs `lakatos refute`: `@ensures` annotations become fast-check property tests, generated into the target project's per-run artifact mirror and executed with vitest; failures come back as per-annotation issues the CLI maps to SZS statuses (`falsified` → CounterSatisfiable, `threw` → Error, `exhausted` → GaveUp).

Unlike thales, pabst has no toolchain, lockfile, or package of its own — it is root-package code. Build (`npm run build`), test (`npm test`), and typecheck all run from the repo root; only its library tests live here (`tests/`).

Annotation parsing is NOT here: discovery, `@ensures` extraction, and prefix/formula parsing live in `lemma/` at the repo root. Pabst consumes lemma's parsed output (`Binder`, `Formula`) and owns only what is fast-check-specific.

## Pipeline

`lakatos refute` (root `src/cli.ts`) drives:

1. **Build specs** (`build-spec.ts`) — lemma's `extract` → `parsePrefix` → `parseBody`, then pabst's `lowerTop` flattens the formula to JS boolean-expression text (a top-level implication's antecedents become `fc.pre` discards) and `free-idents.ts` classifies each atom's free identifiers as bound, global, or module export (unresolvable names are rejected). Result: one flat `PropertySpec` per annotation. An annotation whose only blocker is a binder domain lemma cannot represent — an interval endpoint beyond the safe integer range, whether or not the clamp empties it — yields no spec at all: generating over the clamped domain would refute a narrower statement than the one written, so it becomes an `untried` entry the CLI reports as `NotTried` with kind `unsupported-range`, exactly as the prover does. The classification and its reason string are lemma's (`clampedEndpoints`, `unsupportedRangeReason`), so the two engines cannot diverge on which domains they refuse.
2. **Codegen** (`codegen.ts` + `emit.ts`) — per source file: mirror path under the run directory's `pabst/` (source extension kept: `a.ts` → `<run>/pabst/a.ts.pabst.test.ts`), then string-build a vitest/`@fast-check/vitest` test file: one `test.prop` per spec, arbitraries rendered from binders by `domains.ts` (`arbitraryFor`, on top of lemma's bounds helpers), a fixed 32-bit seed (`seed.ts`, `--seed` to reproduce).
3. **Run** (`run.ts`) — spawn `npx vitest run --reporter=json` and classify the outcome: `completed` (JSON results), `no-results`, or `broken-run`.
4. **Report** — the CLI decodes sentinel-framed issues out of the vitest JSON (`contract.ts`) and joins them into the envelope.

## The wire contract (`contract.ts`)

Generated tests import `bool` and `report` from **`lakatos/runtime`** (`runtime.ts`, the root package's only export subpath — it resolves from the _target project's_ node_modules, which is why refute must run from that project). A failing property throws an `Issue` encoded behind the `PABST_ISSUE:` sentinel; `parseIssue` recovers it from vitest's failure messages. Every string that must agree across emitted test ↔ runtime ↔ CLI decoder lives in `contract.ts`, and `tests/contract-pins.test.ts` pins the ones that reach outside (the runtime specifier and dist paths, the issue schema's `functionName` pattern against lemma's `QUALIFIED_NAME_PATTERN`). If you change a contract string, the pin test tells you every other spelling to update.

`schemas/issue.schema.json` is the per-issue JSON Schema; `IssueKind` is `falsified | threw | exhausted`. The SZS mapping itself lives in root `src/szs.ts`, not here.

## Conventions

- **Generated code is disposable.** Every run writes a fresh directory and never hand-edits one; determinism comes from the seed.
- **Engine-neutral logic goes to `lemma/`, fast-check-specific logic stays here.** `domains.ts` renders arbitraries from lemma's bounds; it should not re-derive bounds arithmetic.
- **Errors that are the input's fault throw `LemmaError`** (the CLI maps it to exit 2 with a one-line diagnostic); anything else escaping is an internal bug. A domain that is merely unrepresentable is not the input's fault: it is contained per annotation as `untried`, never a run-level abort.
- **Never depend on thales** (and vice versa); the only sharing is via `lemma/` and the root contract. See the root `CLAUDE.md` for the layering rules.

CI: the root `lakatos.yml` workflow covers pabst (its tests are part of the root vitest suite), and Stryker mutation testing covers its sources.
