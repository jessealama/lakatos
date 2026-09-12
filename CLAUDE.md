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


<!-- BEGIN BEADS INTEGRATION v:1 profile:minimal hash:6cd5cc61 -->
## Beads Issue Tracker

This project uses **bd (beads)** for issue tracking. Run `bd prime` to see full workflow context and commands.

### Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --claim  # Claim work
bd close <id>         # Complete work
```

### Rules

- Use `bd` for ALL task tracking — do NOT use TodoWrite, TaskCreate, or markdown TODO lists
- Run `bd prime` for detailed command reference and session close protocol
- Use `bd remember` for persistent knowledge — do NOT use MEMORY.md files

**Architecture in one line:** issues live in a local Dolt DB; sync uses `refs/dolt/data` on your git remote; `.beads/issues.jsonl` is a passive export. See https://github.com/gastownhall/beads/blob/main/docs/SYNC_CONCEPTS.md for details and anti-patterns.

## Agent Context Profiles

The managed Beads block is task-tracking guidance, not permission to override repository, user, or orchestrator instructions.

- **Conservative (default)**: Use `bd` for task tracking. Do not run git commits, git pushes, or Dolt remote sync unless explicitly asked. At handoff, report changed files, validation, and suggested next commands.
- **Minimal**: Keep tool instruction files as pointers to `bd prime`; use the same conservative git policy unless active instructions say otherwise.
- **Team-maintainer**: Only when the repository explicitly opts in, agents may close beads, run quality gates, commit, and push as part of session close. A current "do not commit" or "do not push" instruction still wins.

## Session Completion

This protocol applies when ending a Beads implementation workflow. It is subordinate to explicit user, repository, and orchestrator instructions.

1. **File issues for remaining work** - Create beads for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **Handle git/sync by active profile**:
   ```bash
   # Conservative/minimal/default: report status and proposed commands; wait for approval.
   git status

   # Team-maintainer opt-in only, unless current instructions forbid it:
   git pull --rebase
   git push
   git status
   ```
5. **Hand off** - Summarize changes, validation, issue status, and any blocked sync/commit/push step

**Critical rules:**
- Explicit user or orchestrator instructions override this Beads block.
- Do not commit or push without clear authority from the active profile or the current user request.
- If a required sync or push is blocked, stop and report the exact command and error.
<!-- END BEADS INTEGRATION -->
