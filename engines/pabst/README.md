# Pabst: A blue-ribbon approach to **P**roperty-**B**ased **T**esting

Pabst is lakatos's refutation engine. Annotate your functions with
properties they're supposed to have, then try to invalidate them with
[fast-check](https://fast-check.dev/).

Put the properties your functions should have in a JSDoc comment, run
`lakatos refute` (the CLI lives at the repo root), and get either "cases
passed" or a counterexample that shows the property doesn't hold.

_Example_ Look at this code. We're trying to assert that the value of the function is
non-zero provided the second argument is an integer. Can you spot the error?

```ts
/**
 * @ensures{nonzero} forall (x: bigint) (y: number) {
 *   Number.isInteger(y) ==> foo(x, y) !== 0
 * }
 */
export function foo(x: bigint, y: number): number {
  return Number(x % 2n) + (y % 2) + 1;
}
```

Each remainder looks like it should be 0 or 1, so the sum looks like it's at
least 1. But JavaScript's `%` returns _negative_ remainders for negative
operands: `foo(-1n, 0)` is `-1 + 0 + 1 === 0`. You don't have to spot that —
`lakatos refute` falsifies the property and reports a counterexample.

## Philosophy

Pabst is a property-based testing tool. Instead of checking
your function against a handful of hand-picked examples,
pabst (delegating to `fast-check`) generates many random
inputs and works hard to **refute** the property you
attached; when it succeeds, it shrinks the failure to a
small, readable counterexample. One thing should be
understood, though: failing to invalidate a property — even
across many runs — is no _proof_ that the property holds. It
is evidence that it holds, but the property might still be
false on inputs the generator never tried. If your goal is
to prove the absence of counterexamples, you need
proof-based tools such as
[Thales](../thales/), this repository's proof engine. That said,
property-based testing is a powerful technique that exposes
a lot of bugs for very little effort, and it sits
comfortably alongside proof-based approaches.

## Getting it

Pabst is not a standalone package: it ships inside the `lakatos` npm
package at this repository's root, which owns the CLI (`lakatos refute`),
the dependency declarations, and the version number. (Through 0.13.0 it
was published standalone as `pabst-checker`; that line has ended.)

Pabst bundles its own [vitest](https://vitest.dev/) and declares
[fast-check](https://fast-check.dev/) as a peer dependency (npm installs
it for you), so nothing else is needed. The peer relationship means pabst
validates your annotations against the same fast-check copy the generated
tests run with — if your project pins an incompatible fast-check, npm says
so at install time instead of your tests failing mysteriously.

## Usage

```bash
lakatos refute                             # discover sources, test, print a JSON report
lakatos refute <files-or-globs>            # same, on an explicit file list
lakatos refute --seed <n> <files-or-globs> # reproduce a prior run's generation
```

With no file arguments, lakatos discovers your sources: exactly the files
`tsc` would compile for `tsconfig.json`. Without a tsconfig, or with one that
names no files, it exits with an error asking for an explicit glob (the type
gate refuses anything outside the tsconfig's program, so there is nowhere
else to look). Discovery stays inside the current directory — a
tsconfig reaching outside it (say, a monorepo `include` of `../shared`) has
those files skipped; run lakatos in the package that owns them.

Declaration files (`.d.ts`) are skipped by default — tsc copies JSDoc into
them, so scanning both a declaration and its source would extract every
property twice. A pattern that explicitly names declarations
(`lakatos refute "index.d.ts"`) is honored, for packages whose hand-written
types are the source.

Pabst writes the test files it generates into a `.lakatos/` directory in your
project, under one subdirectory per invocation named for the run's start time
(`.lakatos/2026-08-17T12-53-06.896Z/pabst/`, matching the `startedAt` the
report carries). Nothing there is ever reused, so there is no reason to commit
it — add `.lakatos/` to your `.gitignore`:

```gitignore
.lakatos/
```

No run is ever written over another: two invocations that start in the same
millisecond get `...943Z` and `...943Z-2`, and the progress line on stderr
names whichever one this run took. Runs accumulate — lakatos never deletes an
earlier one, so you can still read the artifacts behind yesterday's report.
Delete the directory when you want the space back.

## Output

`lakatos refute` prints a single JSON envelope to **stdout**; **stderr**
carries only progress and crashes. The envelope's shape — one entry per
annotation, each with an SZS status — is documented in the
[root README](../../README.md) and pinned by
[`schemas/envelope.schema.json`](../../schemas/envelope.schema.json). The
failure detail pabst attaches to a flagged annotation is the engine's own
issue format ([`schemas/issue.schema.json`](schemas/issue.schema.json)):

```json
{
  "file": "src/math.ts",
  "function": "add",
  "property": "commutes",
  "kind": "falsified",
  "counterexample": { "x": 1, "y": 2 }
}
```

- `kind` is `"falsified"` (returned `false`), `"threw"` (raised an exception —
  see `error`), `"exhausted"` (too many precondition skips — `error` explains,
  and there is no `counterexample`), or `"budget"` (an enumerated domain outran
  its wall-clock budget: `reason` says how far the walk got, and there is no
  `counterexample`).
- Counterexample values are JSON-native where they round-trip; bigints and
  non-finite numbers appear as fast-check strings (e.g. `"1n"`).
- The `seed` is generated per run and echoed back; pass it to `--seed` to
  reproduce a failing run exactly.

A property whose binders range over at most 1,000 tuples (booleans, bounded
`int`/`nat`/`bigint` intervals) is not sampled at all: the generated test
walks every tuple, ascending per binder and lexicographic across binders,
so a clean pass reports `Theorem` and a failure reports the least tuple.
Number, string, and class binders always sample.

The process exits `0` when nothing was flagged, `1` when at least one
annotation was, and `2` on usage errors — including annotation errors such
as a malformed formula, an unsupported domain, or a reference to an
unexported symbol, which are reported as a one-line message on stderr.

## Grammar

The normative grammar lives in [`spec/grammar.ebnf`](../../spec/grammar.ebnf);
this section is the guided tour.

A property is a universally quantified formula in Pabst's **logic surface**.
Non-ASCII symbols are the canonical form; most have ASCII fallbacks
(negation `¬` and the equation glyphs `≡`/`≢` are glyph-only — the ASCII
spelling of an equation is a plain `Object.is` call).

```ts
/**
 * @ensures{guarded} forall (x: int) {
 *   isPrime(x) ∧ x > 2 → isOdd(x)
 * }
 */
```

- **Quantifier:** `forall` / `∀`, one-or-more binder groups, then the body
  in braces: `forall (x: int) { ... }`. Lean-style grouping `(x y: int)` is
  supported. Existential `∃` / `exists` is intentionally rejected (PBT
  cannot soundly confirm existence).
- **Domains:** `int`, `nat`, `number`, `boolean`, `string`, `bigint`.
  A numeric domain (`int`, `nat`, `number`, `bigint`) may be constrained to
  an interval: `forall (x: int ∈ [1, 30])` (ASCII fallback: `in`). Each
  bound is independently inclusive (`[`/`]`) or exclusive (`(`/`)`), so
  `(0, 1]`, `[0, 30)`, and `(0, 30)` all work — for `int`/`nat`/`bigint`
  an exclusive bound is a ±1 adjustment. An endpoint may be unbounded:
  `-∞`/`∞` (ASCII: `Infinity`), so `(x: number ∈ (0, ∞))` is a strictly
  positive number (excluding `-0` — and `Infinity`, since the bound is
  exclusive; `[0, ∞]` may generate `Infinity` itself). For `int`, `nat`,
  and `bigint` an ∞ endpoint must be exclusive; for `int`/`nat` it means
  the safe integer limit (±2^53 − 1), and a finite endpoint beyond that
  limit clamps to it with a warning. A `nat` interval reaching below 0
  clamps to 0 (`(-2, 5]` and `(-∞, 5]` denote the same naturals).
  `number` intervals follow fast-check's double ordering, in which every
  double is distinct: `-0` sits below `0`, and an exclusive bound removes
  exactly one adjacent double — so `[-1, 0)` can generate `-0` (which
  `== 0`), and `(-0, 0]` is the singleton `{0}`. A bounded `number` never
  generates `NaN`.
- **Regex guards** constrain a string binder to strings matching a JS
  regular expression: `forall (s: string ∈ /[a-z]+/)` (ASCII fallback:
  `in`). Membership means the _whole_ string matches — pabst anchors the
  pattern for you (lowering to `fc.stringMatching(/^(?:[a-z]+)$/)`), so
  `/[a-z]+/` never generates `"3fk!"`. Flags `s` and `u` are allowed (`u`
  enables `\p{...}` escapes); everything else is rejected — `m` because it
  would reintroduce substring matching, `i`/`v` because fast-check's
  generator lacks them, `g`/`y`/`d` because they don't affect generation.
  Patterns outside fast-check's supported subset (lookarounds,
  backreferences, `\b`) are compile-time errors. Careful inside JSDoc: a
  `*/` in a pattern (e.g. the trailing star in a pattern matching
  zero-or-more) ends the comment early — write `{0,}` instead of a
  trailing `*`, or wrap it in `(?:...)`.
- **Connectives** (tightest→loosest): `¬` > `∧` > `∨` > `→` > `↔`.
  Fallbacks: `∧`=`/\`, `∨`=`\/`, `→`=`->`/`==>`, `↔`=`<->`/`iff`.
  Negation `¬` is glyph-only.
- **Equations:** `A ≡ B` means identity — sugar for `Object.is(A, B)`;
  `A ≢ B` is its negation. Both are glyph-only, like `¬`: in plain ASCII,
  call `Object.is(A, B)` directly (negate at an atom's top level with `≢` or
  `¬(Object.is(A, B))`; nested `!Object.is(A, B)` is fine). This is
  SameValue, not mathematical equality: `NaN ≡ NaN` holds and `-0 ≡ 0` does
  not, so `x + 0 ≡ x` is refutable at `x = -0` (guard with `x ≢ -0 →` if
  that is intended).
  An equation lives at the **top level of an atom** — it splits the atom
  into two JS sides. In nested positions (callbacks, call arguments,
  template substitutions), call `Object.is` directly:
  `xs.every(x => Object.is(x, 0))`, not `xs.every(x => x ≡ 0)`.
  An unparenthesized `??` or ternary beside `≡` is an error — parenthesize
  the intended grouping, e.g. `a ≡ (b ?? c)` or `a ≡ (b ? c : d)`.
  Chains like `a ≡ b ≡ c` are errors — write
  `a ≡ b ∧ b ≡ c`. Loose `==`/`!=` are errors (use `≡`/`≢` or `===`/`!==`);
  `===`/`!==` keep their exact JS meaning; assignments — plain `=` and
  compound forms like `+=` — cannot appear in a formula (default-parameter
  initializers in callbacks are fine); `≠` is rejected with a hint to
  write `≢`.
- **Atoms are JavaScript** and must be genuine booleans — every atom is checked
  at runtime (`5 ∧ true` is an error, not a coercion). You may **not** use JS
  `&&`/`||`/`!` at an atom's top level — use the glyphs. They remain legal
  _inside_ a leaf (e.g. a callback `xs.every(x => x > 0 && x < 10)`).
- **Implication discard:** a **top-level** `→`'s antecedents become `fc.pre(...)`
  (QuickCheck-style discarded cases, reported as `exhausted` if too many skip);
  a **parenthesised** `→` is ordinary material implication `¬P ∨ Q`.
- **Biconditional** `↔` is non-associative (parenthesise chains) and is _not_ a
  discard — it lowers to boolean equality.
- **Scoping:** every symbol an atom references must be `export`ed from its module.

Each `@ensures{name}` becomes one issue (keyed by file, function, and property
name) if it fails. Generated files land in the run's own directory (see
[Usage](#usage)) mirroring the source tree; they must never be hand-edited.

## Development

Pabst is built and tested as part of the root `lakatos` package — run
everything from the repository root:

```bash
npm install
npm test          # vitest (root suite, includes engines/pabst/tests)
npm run build     # tsc -> dist/
```

Requires Node 24+.
