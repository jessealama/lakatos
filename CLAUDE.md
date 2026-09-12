# CLAUDE.md

Monorepo for lakatos: proofs and refutations for TypeScript. `README.md` (Layout, Architecture) is the tour; each engine's own `CLAUDE.md` loads when you work under it.

Start from `src/cli.ts` (the `prove|refute|check` spine; `check` is still a NotTried stub) and `src/envelope.ts` + `src/szs.ts` (the per-annotation output contract, schema in `schemas/`).

## Layering

`engines/thales/` (proofs, Lean) and `engines/pabst/` (refutations, fast-check) never depend on each other. Both may depend on `lemma/` (the Lemma annotation language: discovery, `@ensures` extraction, parsing; spec and conformance corpus in `spec/`), which depends on no engine. `src/` may depend on all of them. One product, one version: `engines/thales/package.json` is private dev tooling for its check scripts, not a second package.

## Building and testing

Every TypeScript part — `src/`, `lemma/`, pabst, thales's `frontend/` — is one root npm package: build, typecheck, test, and format from the repo root. Only thales's Lean side has its own toolchain and lake project; run `lake` from `engines/thales/`. `lakatos prove` needs a lakatos checkout with the Lean toolchain; the prove e2e and verdict corpus run only under `LAKATOS_PROVE_E2E=1` (CI: `thales.yml`; `lakatos.yml` covers the TypeScript suites, typecheck, format, and a coverage gate).

## Issue tracker

GitHub Issues on `jessealama/lakatos`. Conventions: `engines/thales/docs/agents/issue-tracker.md`; triage labels: `engines/thales/docs/agents/triage-labels.md`.

## Docs

Design records spanning more than one component go in `docs/design/`; a single engine's notes stay under that engine (`engines/thales/docs/`). Records are dated and are not updated to track the code.
