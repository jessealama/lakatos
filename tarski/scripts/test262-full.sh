#!/bin/sh
# The scheduled whole-suite run, and the way to reproduce it by hand.
#
# `tarski.yml`'s `full-run` job runs this and nothing else, and
# `tarski/CLAUDE.md` tells a person to run the same line, so the slices,
# the per-test timeout, and the overall budget cannot drift apart between
# the two. It writes `test262/results.md` and `test262/results.json`; the
# workflow commits them when they changed.
#
# `annexB` (sloppy-mode and legacy web semantics) and `staging` are
# outside the epic's denominator on purpose; `intl402` is inside the run
# so its count lands among the excluded kinds rather than vanishing.
#
# The checkout is `LAKATOS_TEST262` when it is set and `tarski/.test262`
# otherwise, and the runner labels the table with the commit it is really
# at. `TEST262_TIMEOUT_MS` and `TEST262_BUDGET_MS` override the per-test
# timeout and the run's wall-clock budget; a test past the budget is
# counted as not run for `budget`, so a truncated run says so.
#
# Needs `npm run build` at the repo root and `lake build tarski` here.
set -eu
cd "$(dirname "$0")/.."
exec node ../dist/tarski/frontend/src/test262/cli.js \
  test/language test/built-ins test/intl402 \
  --summary \
  --timeout "${TEST262_TIMEOUT_MS:-10000}" \
  --budget "${TEST262_BUDGET_MS:-14400000}" \
  --markdown test262/results.md \
  --json test262/results.json \
  "$@"
