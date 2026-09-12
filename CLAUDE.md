# CLAUDE.md

Monorepo for lakatos: proofs and refutations for TypeScript. `README.md` (Layout, Architecture) is the tour; each engine's own `CLAUDE.md` loads when you work under it.

Start from `src/cli.ts` (the `prove|refute|check` spine; `check` is still a NotTried stub) and `src/envelope.ts` + `src/szs.ts` (the per-annotation output contract, schema in `schemas/`).

## Layering

`engines/thales/` (proofs, Lean) and `engines/pabst/` (refutations, fast-check) never depend on each other. Both may depend on `lemma/` (the Lemma annotation language: discovery, `@ensures` extraction, parsing; spec and conformance corpus in `spec/`), which depends on no engine. `src/` may depend on all of them. One product, one version: `engines/thales/package.json` is private dev tooling for its check scripts, not a second package.

## Building and testing

Every TypeScript part — `src/`, `lemma/`, pabst, thales's `frontend/` — is one root npm package: build, typecheck, test, and format from the repo root. Only thales's Lean side has its own toolchain and lake project; run `lake` from `engines/thales/`. `lakatos prove` needs a lakatos checkout with the Lean toolchain; the prove e2e and verdict corpus run only under `LAKATOS_PROVE_E2E=1` (CI: `thales.yml`; `lakatos.yml` covers the TypeScript suites, typecheck, format, and a coverage gate).

## Issue tracker

GitHub Issues on `jessealama/lakatos` is the tracker: bugs, features, triage, and everything a PR or design record refers to by number. Conventions: `engines/thales/docs/agents/issue-tracker.md`; triage labels: `engines/thales/docs/agents/triage-labels.md`.

Beads (`bd`, below) is agent-local task tracking within a session, not a second issue tracker: a bead is a step toward an issue, never a substitute for filing one.

## Docs

Design records spanning more than one component go in `docs/design/`; a single engine's notes stay under that engine (`engines/thales/docs/`). Records are dated and are not updated to track the code.

<!-- BEGIN BEADS INTEGRATION v:1 profile:minimal hash:6cd5cc61 -->

## Beads (agent task tracking)

`bd` tracks an agent's in-session tasks and handoffs. Run `bd prime` for the command reference.

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --claim  # Claim work
bd close <id>         # Complete work
```

- Use `bd` instead of TodoWrite, TaskCreate, or markdown TODO lists for task tracking; anything that outlives the session goes to GitHub Issues.
- Persistent memory stays in Claude Code's own memory files; do not use `bd remember` for it.
- Issues live in a local Dolt DB; sync uses `refs/dolt/data` on the git remote; `.beads/issues.jsonl` is a passive export. Never commit, push, or sync Dolt unless asked.
- At session end: close finished beads, file GitHub issues for follow-up work, run the local gate if code changed, and report changed files and status before any commit or push.

<!-- END BEADS INTEGRATION -->
