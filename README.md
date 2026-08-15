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

The name is from Imre Lakatos's *Proofs and Refutations*: mathematics
advances by conjectures, attempted proofs, and counterexamples that force
the conjecture to be repaired. That loop is exactly what this tool runs.

## Status

Design phase. The two engines exist and work today; this frontend does not
yet. This README describes the committed design.

## Architecture

Lakatos is a thin frontend over two engines, one per side of the dialectic:

```
                 lakatos  (CLI, npm)
                /        \
        refute /          \ prove
              v            v
           pabst         thales
     (TypeScript;       (Lean 4; pinned binary bundle,
      npm dependency;    auto-downloaded to ~/.thales
      fast-check)        on first use)
```

- [pabst](https://github.com/jessealama/pabst) — the refutation engine:
  compiles properties to [fast-check](https://fast-check.dev/) runs.
- [thales](https://github.com/jessealama/thales) — the proof engine: a
  TypeScript-to-Lean 4 compiler with a graded automatic discharge ladder
  (exhaustive checking on bounded domains, then a fixed tactic stack, then
  an honest "unable to prove").

The engines never depend on each other. Neither requires you to install
Lean: thales ships as a prebuilt per-platform bundle that lakatos pins and
fetches once, Playwright-style.

Properties are written in
[Lemma](https://github.com/jessealama/lemma-lang), a little specification
language embedded in JSDoc — annotated files remain ordinary TypeScript
accepted by `tsc --strict`.

## Commands

- **`lakatos check <file>`** — the flagship: refute first (fast — catches
  false properties in seconds), then prove, then report one graded verdict
  per property.
- `lakatos prove <file>` — proof engine only.
- `lakatos refute <file>` — refutation engine only. Note the semantics:
  the command names the *attempt*; finding no counterexample is success
  (exit 0), like any test run.

## Verdicts

Human-readable verdicts lead; each carries an
[SZS ontology](https://tptp.org/UserDocs/SZSOntology/) status as metadata
(in detail lines and in `--json` output), shared with both engines'
own output:

| Verdict | SZS status | Meaning |
|---|---|---|
| PROVED | `Theorem` | Holds for all inputs. Any assumptions (opaque callees, assumed contracts) are listed with the verdict — the trust boundary is impossible to miss. |
| REFUTED | `CounterSatisfiable` | A concrete counterexample was found and is reported. |
| TESTED, not proved | `Unknown` | The refuter found nothing in its budget and the prover gave up; per-engine sub-statuses (`GaveUp`, `Timeout`) say why. |

Exit codes are deliberately boring: `0` — no property refuted; `1` — at
least one property refuted (or a counterexample found by the prover);
`2` — input or usage error. "Tested but not proved" exits `0` with a
diagnostic: an unproved truth is not a failure.

## License

MIT.
