# CLAUDE.md

## What this package is

Tarski is lakatos's JS-semantics library: the Lean definitions that give TypeScript's values and operations their meaning. `lakatos prove` (thales) proves `@ensures` properties against models built from these definitions. The package is shared: thales requires it by path (`require tarski from "../../tarski"` in `engines/thales/lakefile.lean`); no engine may be required by it. The boundary rule: nothing here mentions `ThalesDsl` or any emission concern — lakatos owns syntax and search, this library owns meaning.

It holds two things over one set of definitions. `Js/` is the semantics library. `Tarski/` is an evaluator for a fragment of JavaScript — a definitional interpreter whose every primitive operation _is_ one of the library's, so a `Theorem` and a run appeal to the same meaning. The evaluator's parser is not in Lean: `frontend/` is a TypeScript bridge over tsc that emits ESTree JSON, and `schemas/tarski-estree.schema.json` at the repo root is the seam. Growing the evaluator is GitHub epic #376.

The Lean toolchain pin is `lean-toolchain` here; `engines/thales/lean-toolchain` is a symlink to it. `lake-manifest.json` is tracked.

## Common commands

From `tarski/`:

```bash
lake build                          # the Js library, the evaluator, the binary
lake build tarski                   # just the evaluator's binary
lake build TarskiTest               # the Lean tests under Test/Js/ and Test/Tarski/
lake env lean Test/Js/NormTest.lean # one test file in isolation
```

The binary lands at `.lake/build/bin/tarski` and takes one ESTree document:

```bash
node ../dist/tarski/frontend/src/bridge-cli.js t.js t.json   # after npm run build
.lake/build/bin/tarski run t.json
```

The bridge and its tests are part of the repo-root npm package, not this lake package: build, typecheck, test, and format them from the repo root.

Wrap `lake env lean` in a timeout when running it by hand; a bad artifact can grind indefinitely.

## Modules

| Module                                                                | Role                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| --------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Js.lean`                                                             | The umbrella import: every module below, in dependency order. Artifacts and tests `import Js`.                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Js/Runtime.lean`, `Js/Number/Basic.lean`                             | The domain: `JsM α := Except JsError α`, `JsNumber := Float`, `floatNaN`. **Computability is the invariant** — `decide` must evaluate models over bounded domains.                                                                                                                                                                                                                                                                                                                                                           |
| `Js/Val.lean`                                                         | The tagged `JsVal` domain for unions, optionals, and booleans: `toNumber`/`toBoolean` (throwing projections), `typeof`, `strictEq`, `sameValue`.                                                                                                                                                                                                                                                                                                                                                                             |
| `Js/Binders.lean`                                                     | Binder-domain meaning: `floatInf` and `ballIco` (bounded ∀ over `[lo, hi)`) with its `Decidable` instance. The witness scans live in the prover, not here.                                                                                                                                                                                                                                                                                                                                                                   |
| `Js/Norm.lean` (+ `Js/NormAttr.lean`)                                 | The `js_norm` simp set: what lets pure-looking code shed its monadic wrapping so the closers see bare arithmetic; dual-tagged for grind. A lowered branch is split into one obligation per arm carrying its condition — the only shape in which a literal arm becomes a ground term. Vanilla Lean has no binary64 theory, so each recurring residual goal is one lemma to add here. `NormAttr` registers the attribute one module below the lemmas, since a simp set is only usable in modules that import its registration. |
| `Js/Number/FloatOps.lean`, `Constants.lean`                           | Binary64 operations JS has and Lean does not (`tsRem`, the roundings, `tsSign`, `tsFround`, `tsMin`/`tsMax`, the integer predicates, `sameValue`) and the `Math`/`Number` constants under their source spellings. Built from `Float.Model`, never `extern`, so the kernel can reduce them; `MAX_VALUE`/`MIN_VALUE` are spelled by bits because their decimals do not reduce.                                                                                                                                                 |
| `Js/Number/FloatFacts.lean`, `FloatOpsFacts.lean`, `FroundFacts.lean` | Kernel-checked theory about binary64 and the models above (monotonicity against a bounded constant, order transitivity and totality away from NaN, the roundings' and clamps' defining inequalities). Residual goals are over `Float`, whose every op is `pack (op (unpack ..))`, so an `UnpackedFloat` fact reaches one only through the `Canonical` round-trip. `FroundFacts` is the order theory of `Math.fround`: each stage of the narrowing is monotone on values, so the composite is.                                |

## The evaluator

| Module               | Role                                                                                                                                                                                                                                                                                                                                                                  |
| -------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Tarski.lean`        | The umbrella import, in dependency order, as `Js.lean` is for the library.                                                                                                                                                                                                                                                                                            |
| `Tarski/Ast.lean`    | The evaluated fragment's syntax. Each constructor's doc comment names the ESTree node it decodes from, so the AST, the decoder, and the schema are readable against one another.                                                                                                                                                                                      |
| `Tarski/Value.lean`  | `Value`, `Obj`, `Cell`, `Heap`, `Env`, `Completion` — the domain, shaped now for the slices that will need it. **Bindings are heap cells, not environment entries**: that is what makes an assignment inside a loop visible after it, and what a closure will capture.                                                                                                |
| `Tarski/Monad.lean`  | `EvalM := StateT Heap (ExceptT Completion Option)`. The `Option` is divergence, and **nothing writes it by hand** — it is only the fixpoint's bottom.                                                                                                                                                                                                                 |
| `Tarski/Eval.lean`   | The interpreter: one `mutual` block under `partial_fixpoint`, so its equations are theorems and no fuel parameter exists. Primitive operations delegate to `Js`; the non-recursive helpers sit outside the block so `simp` may use them freely. **`evalWhile`'s equation never joins a simp set** — a loop is unfolded one iteration at a time with `rw [evalWhile]`. |
| `Tarski/Decode.lean` | `Lean.Json` → `Program`, written to the schema. The only place that says `unsupported`, and the only module importing `Lean.Data.Json`.                                                                                                                                                                                                                               |
| `Tarski/Format.lean` | Provisional `Value → String` for the binary; **not** ECMA `Number::toString`, and isolated so #388 replaces one file.                                                                                                                                                                                                                                                 |
| `Tarski/Main.lean`   | `tarski run <file.json>`. Exit codes are documented in its header: 0 ran, 1 uncaught, 2 bad input, 3 unsupported. Divergence is not one — the caller imposes a timeout.                                                                                                                                                                                               |
| `frontend/src/`      | The parser bridge (`estree.ts`) and its command (`bridge-cli.ts`). A construct outside the fragment becomes an `Unsupported` node in place, so the document still validates and **Lean owns every refusal verdict**.                                                                                                                                                  |

## Tests

`Test/Js/` and `Test/Tarski/` — Lean unit tests, one file per concern; `lake build TarskiTest` builds them all and each runs alone via `lake env lean`. Library test files import only `Js` and its submodules.

`Test/Tarski/fixtures/numeric-loop.json` is the parser bridge's output byte for byte; `tarski/frontend/tests/bridge-cli.test.ts` holds the two copies together, and the tarski workflow runs the binary on it. The bridge's own tests are vitest, run from the repo root.
